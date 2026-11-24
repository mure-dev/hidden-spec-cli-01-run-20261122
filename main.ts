// main.ts is mend, the CLI SPEC.md specifies (MIT). Node 22, the standard library alone;
// run it as `node main.ts [options] [PATCH]`.
//
// It reads a patch in one of four formats (unified diff, SEARCH/REPLACE blocks, V4A, JSON
// edits), finds the lines each edit names at the first of three matching tiers, and writes
// every change or none, printing what it changed or why it failed. SPEC.md is the contract.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file
// hands over to runner.ts (the last lines below): keep that hand-over and runner.ts as they are.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** A file's lines, its line break and whether it ends with one (SPEC.md section 3). */
interface FileState {
  lines: string[];
  br: '\r\n' | '\n';
  finalBreak: boolean;
}

function parseFile(text: string): FileState {
  if (text === '') return { lines: [], br: '\n', finalBreak: false };
  const nl = text.indexOf('\n');
  const br: '\r\n' | '\n' = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const finalBreak = text.endsWith(br);
  if (finalBreak) parts.pop();
  return { lines: parts, br, finalBreak };
}

function serializeFile(f: FileState): string {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.br) + (f.finalBreak ? f.br : '');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: Array<{ from: string; to: string }> = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/* Section 5: matching lines at three tiers. */

function trimEndWs(s: string): string {
  return s.replace(/[ \t]+$/, '');
}
function trimWs(s: string): string {
  return s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}
function leadingWs(s: string): string {
  const m = /^[ \t]*/.exec(s);
  return m === null ? '' : m[0];
}

function normLine(s: string, tier: number): string {
  if (tier === 0) return s;
  if (tier === 1) return trimEndWs(s);
  return trimWs(s);
}

/** Positions where O occurs in the file's lines at one tier; occurrences may overlap. */
function occurrencesAt(fileLines: string[], O: string[], tier: number): number[] {
  const out: number[] = [];
  if (O.length === 0 || O.length > fileLines.length) return out;
  const On = O.map((l) => normLine(l, tier));
  for (let i = 0; i + O.length <= fileLines.length; i++) {
    let ok = true;
    for (let j = 0; j < O.length; j++) {
      if (normLine(fileLines[i + j]!, tier) !== On[j]) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/** The first tier at which O occurs at least once, with its occurrences; null when none. */
function matchTier(fileLines: string[], O: string[], strict: boolean): { tier: number; occ: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const occ = occurrencesAt(fileLines, O, t);
    if (occ.length > 0) return { tier: t, occ };
  }
  return null;
}

/**
 * The first tier at which O occurs at or after `from`, with the first such occurrence.
 * When eofOnly, only an occurrence ending at the file's last line counts.
 */
function matchTierFrom(fileLines: string[], O: string[], from: number, strict: boolean, eofOnly: boolean): { tier: number; pos: number } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const occ = occurrencesAt(fileLines, O, t).filter((p) => p >= from && (!eofOnly || p + O.length === fileLines.length));
    if (occ.length > 0) return { tier: t, pos: occ[0]! };
  }
  return null;
}

/** One line of N: a context line is written as the file's own matched line. */
interface NewLine {
  text: string;
  ctx: boolean;
  oIndex: number;
}

/** N written over the match at pos: context lines from the file, other lines re-indented at tier 2. */
function applyReplacement(fileLines: string[], pos: number, O: string[], N: NewLine[], tier: number): string[] {
  const F = leadingWs(fileLines[pos] ?? '');
  const P = leadingWs(O[0] ?? '');
  const out: string[] = [];
  for (const item of N) {
    if (item.ctx) {
      out.push(fileLines[pos + item.oIndex]!);
      continue;
    }
    let t = item.text;
    if (tier === 2 && t !== '' && !/^[ \t]+$/.test(t) && t.startsWith(P)) t = F + t.slice(P.length);
    out.push(t);
  }
  return out;
}

/* Section 9: JSON edits. */

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

/* Section 6: unified diffs. */

interface BodyItem {
  kind: 'ctx' | 'old' | 'new' | 'slash';
  text: string;
}

interface Hunk {
  A: number;
  items: BodyItem[];
  O: string[];
  N: NewLine[];
  noFinalBreak: boolean;
}

function buildON(items: BodyItem[]): { O: string[]; N: NewLine[] } {
  const O: string[] = [];
  const N: NewLine[] = [];
  for (const it of items) {
    if (it.kind === 'ctx' || it.kind === 'old') {
      const oIndex = O.length;
      O.push(it.text);
      if (it.kind === 'ctx') N.push({ text: it.text, ctx: true, oIndex });
    } else if (it.kind === 'new') {
      N.push({ text: it.text, ctx: false, oIndex: -1 });
    }
  }
  return { O, N };
}

/** True when a `\` line follows the hunk's last context or `+` line. */
function hunkNoFinalBreak(items: BodyItem[]): boolean {
  for (let k = items.length - 1; k >= 0; k--) {
    const it = items[k]!;
    if (it.kind === 'ctx' || it.kind === 'new') {
      return k + 1 < items.length && items[k + 1]!.kind === 'slash';
    }
  }
  return false;
}

/** A hunk body starting at `start`; returns the hunk and the index after the body. */
function parseHunkBody(lines: string[], start: number, A: number): { hunk: Hunk; next: number } {
  const items: BodyItem[] = [];
  let i = start;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) break;
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
    if (line.startsWith(' ')) {
      items.push({ kind: 'ctx', text: line.slice(1) });
      i++;
      continue;
    }
    if (line.startsWith('-')) {
      items.push({ kind: 'old', text: line.slice(1) });
      i++;
      continue;
    }
    if (line.startsWith('+')) {
      items.push({ kind: 'new', text: line.slice(1) });
      i++;
      continue;
    }
    if (line.startsWith('\\')) {
      items.push({ kind: 'slash', text: line });
      i++;
      continue;
    }
    if (line === '') {
      items.push({ kind: 'ctx', text: '' });
      i++;
      continue;
    }
    break;
  }
  while (items.length > 0) {
    const last = items[items.length - 1]!;
    if (last.kind === 'ctx' && last.text === '') items.pop();
    else break;
  }
  const { O, N } = buildON(items);
  return { hunk: { A, items, O, N, noFinalBreak: hunkNoFinalBreak(items) }, next: i };
}

/** The path after `--- ` or `+++ `: up to the first tab, surrounding spaces removed, a/ or b/ removed. Null for /dev/null. */
function diffPath(s: string): string | null {
  const tab = s.indexOf('\t');
  let t = (tab >= 0 ? s.slice(0, tab) : s).trim();
  if (t.startsWith('a/') || t.startsWith('b/')) t = t.slice(2);
  if (t === '/dev/null') return null;
  return t;
}

interface UnifiedSection {
  oldPath: string | null;
  newPath: string | null;
  diffOld: string | null;
  diffNew: string | null;
  renameFrom: string | null;
  renameTo: string | null;
  hasPair: boolean;
  isNewFile: boolean;
  isDeleted: boolean;
  hunks: Hunk[];
}

const HUNK_RE = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/;
const DIFF_GIT_RE = /^diff --git a\/(\S+) b\/(\S+)/;

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const sections: UnifiedSection[] = [];
  let cur: UnifiedSection | null = null;
  let inHeader = false;
  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const m = DIFF_GIT_RE.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      cur = { oldPath: null, newPath: null, diffOld: m[1]!, diffNew: m[2]!, renameFrom: null, renameTo: null, hasPair: false, isNewFile: false, isDeleted: false, hunks: [] };
      sections.push(cur);
      inHeader = true;
      i++;
      continue;
    }
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      const oldP = diffPath(line.slice(4));
      const newP = diffPath(lines[i + 1]!.slice(4));
      if (cur !== null && inHeader) {
        if (!cur.hasPair) {
          cur.oldPath = oldP;
          cur.newPath = newP;
          cur.hasPair = true;
        }
      } else {
        cur = { oldPath: oldP, newPath: newP, diffOld: null, diffNew: null, renameFrom: null, renameTo: null, hasPair: true, isNewFile: false, isDeleted: false, hunks: [] };
        sections.push(cur);
        inHeader = true;
      }
      i += 2;
      continue;
    }
    if (line.startsWith('@@')) {
      const hm = HUNK_RE.exec(line);
      if (hm === null || cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const A = parseInt(hm[1]!, 10);
      const { hunk, next } = parseHunkBody(lines, i + 1, A);
      cur.hunks.push(hunk);
      inHeader = false;
      i = next;
      continue;
    }
    if (cur !== null && inHeader) {
      if (line.startsWith('--- ')) throw new Exit2(`error: parse ${i + 2}`);
      if (line.startsWith('rename from ')) {
        cur.renameFrom = line.slice('rename from '.length);
        i++;
        continue;
      }
      if (line.startsWith('rename to ')) {
        cur.renameTo = line.slice('rename to '.length);
        i++;
        continue;
      }
      if (line === 'new file mode' || line.startsWith('new file mode ')) {
        cur.isNewFile = true;
        i++;
        continue;
      }
      if (line === 'deleted file mode' || line.startsWith('deleted file mode ')) {
        cur.isDeleted = true;
        i++;
        continue;
      }
      i++;
      continue;
    }
    i++;
  }
  if (sections.length === 0) throw new Exit2('error: parse 1');
  return sections.map((s) => unifiedSectionEdit(s, strict));
}

/** One hunk applied to a file's state; d is the line shift from this section's earlier hunks. */
function applyHunk(state: FileState, h: Hunk, strict: boolean, d: number, path: string): FileState {
  const lines = state.lines;
  if (h.O.length === 0) {
    const at = Math.max(0, Math.min(h.A + d, lines.length));
    const added = h.N.map((n) => n.text);
    const newLines = [...lines.slice(0, at), ...added, ...lines.slice(at)];
    let finalBreak = state.finalBreak;
    if (at === lines.length) finalBreak = !h.noFinalBreak;
    return { lines: newLines, br: state.br, finalBreak };
  }
  const m = matchTier(lines, h.O, strict);
  if (m === null) throw new Fail('no-match', path);
  const target = h.A - 1 + d;
  let pos = m.occ[0]!;
  let best = Math.abs(pos - target);
  for (const o of m.occ) {
    const dist = Math.abs(o - target);
    if (dist < best) {
      pos = o;
      best = dist;
    }
  }
  const replacement = applyReplacement(lines, pos, h.O, h.N, m.tier);
  const newLines = [...lines.slice(0, pos), ...replacement, ...lines.slice(pos + h.O.length)];
  let finalBreak = state.finalBreak;
  if (pos + h.O.length === lines.length) finalBreak = !h.noFinalBreak;
  return { lines: newLines, br: state.br, finalBreak };
}

function unifiedSectionEdit(s: UnifiedSection, strict: boolean): Edit {
  return (tree) => {
    const oldPath = s.hasPair ? s.oldPath : (s.renameFrom ?? s.diffOld);
    const newPath = s.hasPair ? s.newPath : (s.renameTo ?? s.diffNew);
    const isCreate = s.isNewFile || oldPath === null;
    const isDelete = !isCreate && (s.isDeleted || newPath === null);
    if (isCreate) {
      if (newPath === null) return;
      if (!safe(newPath)) throw new Fail('unsafe', newPath);
      if (tree.get(newPath) !== null) throw new Fail('exists', newPath);
      const plus: string[] = [];
      for (const h of s.hunks) for (const it of h.items) if (it.kind === 'new') plus.push(it.text);
      let noFinalBreak = false;
      for (let hi = s.hunks.length - 1; hi >= 0; hi--) {
        const h = s.hunks[hi]!;
        let found = false;
        for (let k = h.items.length - 1; k >= 0; k--) {
          if (h.items[k]!.kind === 'new') {
            noFinalBreak = k + 1 < h.items.length && h.items[k + 1]!.kind === 'slash';
            found = true;
            break;
          }
        }
        if (found) break;
      }
      tree.now.set(newPath, plus.length === 0 ? '' : plus.join('\n') + (noFinalBreak ? '' : '\n'));
      return;
    }
    if (isDelete) {
      if (oldPath === null) return;
      if (!safe(oldPath)) throw new Fail('unsafe', oldPath);
      if (tree.get(oldPath) === null) throw new Fail('missing', oldPath);
      tree.now.set(oldPath, null);
      return;
    }
    if (oldPath === null || newPath === null) return;
    if (oldPath !== newPath) {
      if (!safe(oldPath)) throw new Fail('unsafe', oldPath);
      if (!safe(newPath)) throw new Fail('unsafe', newPath);
      const cur = tree.get(oldPath);
      if (cur === null) throw new Fail('missing', oldPath);
      if (tree.get(newPath) !== null) throw new Fail('exists', newPath);
      let state = parseFile(cur);
      let d = 0;
      for (const h of s.hunks) {
        state = applyHunk(state, h, strict, d, oldPath);
        d += h.N.length - h.O.length;
      }
      tree.now.set(newPath, serializeFile(state));
      tree.now.set(oldPath, null);
      tree.moves.push({ from: oldPath, to: newPath });
      return;
    }
    if (!safe(oldPath)) throw new Fail('unsafe', oldPath);
    const cur = tree.get(oldPath);
    if (cur === null) throw new Fail('missing', oldPath);
    let state = parseFile(cur);
    let d = 0;
    for (const h of s.hunks) {
      state = applyHunk(state, h, strict, d, oldPath);
      d += h.N.length - h.O.length;
    }
    tree.now.set(oldPath, serializeFile(state));
  };
}

/* Section 7: SEARCH/REPLACE blocks. */

interface SRBlock {
  path: string;
  oldLines: string[];
  newLines: string[];
}

function searchReplaceEdits(lines: string[], strict: boolean): Edit[] {
  const blocks: SRBlock[] = [];
  let prevEnd = -1;
  for (let i = 0; i < lines.length; i++) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') continue;
    let eq = -1;
    for (let j = i + 1; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '<<<<<<< SEARCH') break;
      if (lines[j]!.trimEnd() === '=======') {
        eq = j;
        break;
      }
    }
    if (eq < 0) throw new Exit2(`error: parse ${i + 1}`);
    let rep = -1;
    for (let j = eq + 1; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '<<<<<<< SEARCH') break;
      if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
        rep = j;
        break;
      }
    }
    if (rep < 0) throw new Exit2(`error: parse ${i + 1}`);
    let path: string | null = null;
    for (let j = i - 1; j > prevEnd; j--) {
      const t = lines[j]!;
      if (blank(t)) continue;
      const trimmed = t.trim();
      if (trimmed.startsWith('```')) continue;
      path = trimmed;
      break;
    }
    if (path === null) {
      if (blocks.length === 0) throw new Exit2(`error: parse ${i + 1}`);
      path = blocks[blocks.length - 1]!.path;
    }
    blocks.push({ path, oldLines: lines.slice(i + 1, eq), newLines: lines.slice(eq + 1, rep) });
    prevEnd = rep;
    i = rep;
  }
  if (blocks.length === 0) throw new Exit2('error: parse 1');
  return blocks.map((b) => srEdit(b, strict));
}

function srEdit(b: SRBlock, strict: boolean): Edit {
  return (tree) => {
    if (!safe(b.path)) throw new Fail('unsafe', b.path);
    if (b.oldLines.length === 0) {
      if (tree.get(b.path) !== null) throw new Fail('exists', b.path);
      tree.now.set(b.path, b.newLines.length === 0 ? '' : b.newLines.join('\n') + '\n');
      return;
    }
    const cur = tree.get(b.path);
    if (cur === null) throw new Fail('missing', b.path);
    const f = parseFile(cur);
    const m = matchTier(f.lines, b.oldLines, strict);
    if (m === null) throw new Fail('no-match', b.path);
    if (m.occ.length > 1) throw new Fail('ambiguous', b.path);
    const pos = m.occ[0]!;
    const N: NewLine[] = b.newLines.map((t) => ({ text: t, ctx: false, oIndex: -1 }));
    const replacement = applyReplacement(f.lines, pos, b.oldLines, N, m.tier);
    const newLines = [...f.lines.slice(0, pos), ...replacement, ...f.lines.slice(pos + b.oldLines.length)];
    tree.now.set(b.path, serializeFile({ lines: newLines, br: f.br, finalBreak: f.finalBreak }));
  };
}

/* Section 8: V4A patches. */

interface V4AChunk {
  anchor: string | null;
  items: BodyItem[];
  O: string[];
  N: NewLine[];
  eof: boolean;
}

function parseV4AChunks(content: Array<{ text: string; lineNo: number }>): V4AChunk[] {
  const chunks: V4AChunk[] = [];
  let cur: V4AChunk | null = null;
  let seenChunk = false;
  const startChunk = (anchor: string | null): void => {
    cur = { anchor, items: [], O: [], N: [], eof: false };
    chunks.push(cur);
    seenChunk = true;
  };
  for (const { text, lineNo } of content) {
    if (text.startsWith('@@')) {
      const a = text.slice(2).trim();
      startChunk(a === '' ? null : a);
      continue;
    }
    if (text === '*** End of File') {
      if (cur === null) throw new Exit2(`error: parse ${lineNo}`);
      cur.eof = true;
      cur = null;
      continue;
    }
    if (text.startsWith(' ') || text.startsWith('-') || text.startsWith('+') || text === '') {
      if (cur === null) {
        if (seenChunk) throw new Exit2(`error: parse ${lineNo}`);
        startChunk(null);
      }
      const kind: BodyItem['kind'] = text === '' ? 'ctx' : text[0] === ' ' ? 'ctx' : text[0] === '-' ? 'old' : 'new';
      cur!.items.push({ kind, text: text === '' ? '' : text.slice(1) });
      continue;
    }
    throw new Exit2(`error: parse ${lineNo}`);
  }
  for (const c of chunks) {
    const { O, N } = buildON(c.items);
    c.O = O;
    c.N = N;
  }
  return chunks;
}

function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let i = lines.length - 1; i >= 0; i--) {
    if (!blank(lines[i]!)) {
      last = i;
      break;
    }
  }
  if (last < 0 || lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const edits: Edit[] = [];
  let i = first + 1;
  while (i < last) {
    const line = lines[i]!;
    if (blank(line)) {
      i++;
      continue;
    }
    let kind: 'add' | 'delete' | 'update' | null = null;
    let path = '';
    if (line.startsWith('*** Add File: ')) {
      kind = 'add';
      path = line.slice('*** Add File: '.length).trim();
    } else if (line.startsWith('*** Delete File: ')) {
      kind = 'delete';
      path = line.slice('*** Delete File: '.length).trim();
    } else if (line.startsWith('*** Update File: ')) {
      kind = 'update';
      path = line.slice('*** Update File: '.length).trim();
    } else {
      throw new Exit2(`error: parse ${i + 1}`);
    }
    const startLine = i + 1;
    let j = i + 1;
    while (j < last) {
      const l = lines[j]!;
      if (l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ')) break;
      j++;
    }
    const content: Array<{ text: string; lineNo: number }> = [];
    for (let k = i + 1; k < j; k++) content.push({ text: lines[k]!, lineNo: k + 1 });
    while (content.length > 0 && blank(content[content.length - 1]!.text)) content.pop();
    edits.push(v4aSectionEdit(kind, path, startLine, content, strict));
    i = j;
  }
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}

function v4aSectionEdit(kind: 'add' | 'delete' | 'update', path: string, startLine: number, content: Array<{ text: string; lineNo: number }>, strict: boolean): Edit {
  if (kind === 'add') {
    const fileLines: string[] = [];
    for (const { text, lineNo } of content) {
      if (text.startsWith('+')) fileLines.push(text.slice(1));
      else if (text === '') fileLines.push('');
      else throw new Exit2(`error: parse ${lineNo}`);
    }
    return (tree) => {
      if (!safe(path)) throw new Fail('unsafe', path);
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.now.set(path, fileLines.length === 0 ? '' : fileLines.join('\n') + '\n');
    };
  }
  if (kind === 'delete') {
    if (content.length > 0) throw new Exit2(`error: parse ${content[0]!.lineNo}`);
    return (tree) => {
      if (!safe(path)) throw new Fail('unsafe', path);
      if (tree.get(path) === null) throw new Fail('missing', path);
      tree.now.set(path, null);
    };
  }
  let moveTo: string | null = null;
  let idx = 0;
  if (content.length > 0 && content[0]!.text.startsWith('*** Move to: ')) {
    moveTo = content[0]!.text.slice('*** Move to: '.length).trim();
    idx = 1;
  }
  const chunks = parseV4AChunks(content.slice(idx));
  if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${startLine}`);
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (moveTo !== null && !safe(moveTo)) throw new Fail('unsafe', moveTo);
    const cur = tree.get(path);
    if (cur === null) throw new Fail('missing', path);
    if (moveTo !== null && tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
    let state = parseFile(cur);
    let cursor = 0;
    for (const chunk of chunks) {
      if (chunk.anchor !== null) {
        const m = matchTierFrom(state.lines, [chunk.anchor], cursor, strict, false);
        if (m === null) throw new Fail('no-match', path);
        cursor = m.pos + 1;
      }
      if (chunk.O.length === 0) {
        const at = chunk.eof ? state.lines.length : Math.min(cursor, state.lines.length);
        const added = chunk.N.map((n) => n.text);
        state = { lines: [...state.lines.slice(0, at), ...added, ...state.lines.slice(at)], br: state.br, finalBreak: state.finalBreak };
        cursor = at + added.length;
        continue;
      }
      const m = matchTierFrom(state.lines, chunk.O, cursor, strict, chunk.eof);
      if (m === null) throw new Fail('no-match', path);
      const replacement = applyReplacement(state.lines, m.pos, chunk.O, chunk.N, m.tier);
      state = { lines: [...state.lines.slice(0, m.pos), ...replacement, ...state.lines.slice(m.pos + chunk.O.length)], br: state.br, finalBreak: state.finalBreak };
      cursor = m.pos + replacement.length;
    }
    const out = serializeFile(state);
    if (moveTo !== null) {
      tree.now.set(moveTo, out);
      tree.now.set(path, null);
      tree.moves.push({ from: path, to: moveTo });
    } else {
      tree.now.set(path, out);
    }
  };
}

/* Section 1 and 2: the command line, the output and the exit codes; section 10: order and atomicity. */

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    edits = kind === 'json' ? jsonEdits(text, lines) : kind === 'unified' ? unifiedEdits(lines, strict) : kind === 'search-replace' ? searchReplaceEdits(lines, strict) : v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const rows: Array<{ key: string; line: string }> = [];
  const suppressed = new Set<string>();
  for (const m of tree.moves) {
    const wasOld = tree.original(m.from);
    const nowOld = tree.get(m.from);
    const wasNew = tree.original(m.to);
    const nowNew = tree.get(m.to);
    if (wasOld !== null && nowOld === null && wasNew === null && nowNew !== null) {
      rows.push({ key: m.to, line: `R ${m.from} -> ${m.to}` });
      suppressed.add(m.from);
      suppressed.add(m.to);
    }
  }
  const byPath = (a: string, b: string): number => Buffer.compare(Buffer.from(a), Buffer.from(b));
  for (const p of [...tree.now.keys()].sort(byPath)) {
    if (suppressed.has(p)) continue;
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    rows.push({ key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  rows.sort((a, b) => byPath(a.key, b.key) || byPath(a.line, b.line));
  const outLines = rows.map((r) => r.line);
  if (!check) {
    for (const p of [...tree.now.keys()].sort(byPath)) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...outLines, `ok: ${outLines.length} ${outLines.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
