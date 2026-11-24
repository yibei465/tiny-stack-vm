// Tiny stack VM for make.fun's tiny-stack-vm-01 (ISA v1): a faithful interpreter of
// generator/subject/ISA.md in the kit. Runs every program in /input and writes
// /output/<id>/stdout.bin + /output/<id>/exit.txt. No clock, no randomness, no
// environment-dependent behaviour: the same set always answers the same way.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const enc = new TextEncoder();
// Per-opcode pops / pushes / validity, from the ISA's opcode table.
const po = new Uint8Array(256);
const pu = new Uint8Array(256);
const ok = new Uint8Array(256);
const set = (o: number, a: number, b: number): void => { po[o] = a; pu[o] = b; ok[o] = 1; };
for (let o = 0x10; o <= 0x22; o++) set(o, 2, 1); // binary arithmetic / logic / compare
set(0x17, 1, 1); set(0x1b, 1, 1); // NEG, NOT
for (const o of [0, 0x30, 0x33, 0x34]) set(o, 0, 0); // HALT, JMP, CALL, RET
set(1, 0, 1); set(2, 0, 1); // PUSH8, PUSH32
set(3, 1, 0); set(4, 1, 2); set(5, 2, 2); set(6, 2, 3); set(7, 3, 3); // POP DUP SWAP OVER ROT
set(0x31, 1, 0); set(0x32, 1, 0); // JZ, JNZ
set(0x40, 1, 1); set(0x41, 2, 0); // LOAD, STORE
set(0x50, 1, 0); set(0x51, 1, 0); set(0x52, 0, 1); set(0x53, 1, 0); // PRINT PUTC IN EXIT

// ISA limits, from generator/subject/ISA.md.
const STEP_LIMIT = 1000000;
const OUT_LIMIT = 65536;
const STACK_CAP = 256;
const CALL_CAP = 64;
const MEM_WORDS = 256;

// Decode a little-endian signed 16-bit value (jump offsets).
const s16 = (lo: number, hi: number): number => ((lo | (hi << 8)) << 16) >> 16;

function run(p: Uint8Array, inp: Uint8Array): [Uint8Array, number] {
  const n = p.length;
  const D = new Int32Array(STACK_CAP); // data stack
  let sp = 0;
  const C = new Int32Array(CALL_CAP); // call stack
  let cp = 0;
  const M = new Int32Array(MEM_WORDS); // memory
  const out = new Uint8Array(OUT_LIMIT);
  let ol = 0, ip = 0, pc = 0, steps = 0;
  const done = (code: number): [Uint8Array, number] => [out.slice(0, ol), code];
  for (;;) {
    if (steps === STEP_LIMIT) return done(10); // step limit
    if (pc < 0 || pc >= n) return done(9); // pc outside the program
    const op = p[pc];
    if (!ok[op]) return done(5); // unknown opcode
    const imm = op === 1 ? 1 : op === 2 ? 4 : op >= 0x30 && op <= 0x33 ? 2 : 0;
    if (pc + imm >= n) return done(9); // immediate cut off by the program's end
    steps++;
    const next = pc + 1 + imm;
    if (sp < po[op]) return done(2); // stack underflow
    if (sp - po[op] + pu[op] > STACK_CAP) return done(3); // stack overflow
    pc = next;
    switch (op) {
      case 0x00: return done(0); // HALT
      case 0x01: D[sp++] = (p[next - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 0x02: D[sp++] = p[next - 4] | (p[next - 3] << 8) | (p[next - 2] << 16) | (p[next - 1] << 24); break; // PUSH32
      case 0x03: sp--; break; // POP
      case 0x04: D[sp] = D[sp - 1]; sp++; break; // DUP
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; } // SWAP
      case 0x06: D[sp] = D[sp - 2]; sp++; break; // OVER
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; } // ROT
      case 0x17: D[sp - 1] = (-D[sp - 1]) | 0; break; // NEG
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break; // NOT
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1], a = D[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0; // ADD, wraps
        else if (op === 0x11) r = (a - b) | 0; // SUB, wraps
        else if (op === 0x12) r = Math.imul(a, b); // MUL, low 32 bits of the exact product
        else if (op === 0x13) { // DIV, truncated toward zero
          if (b === 0) return done(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) { // MOD, sign of a
          if (b === 0) return done(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) { // DIVU
          if (b === 0) return done(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) { // MODU
          if (b === 0) return done(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b; // AND
        else if (op === 0x19) r = a | b; // OR
        else if (op === 0x1a) r = a ^ b; // XOR
        else if (op === 0x1c) r = a << (b & 31); // SHL
        else if (op === 0x1d) r = a >> (b & 31); // SHR, arithmetic
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0; // SHRU, logical
        else if (op === 0x20) r = a === b ? 1 : 0; // EQ
        else if (op === 0x21) r = a < b ? 1 : 0; // LT, signed
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU, unsigned
        D[sp - 2] = r; sp--;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP, JZ, JNZ
        const rel = s16(p[next - 2], p[next - 1]);
        let take = true;
        if (op !== 0x30) { const v = D[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL
        if (cp === CALL_CAP) return done(7);
        C[cp++] = next;
        pc = p[next - 2] | (p[next - 1] << 8);
        break;
      case 0x34: // RET
        if (cp === 0) return done(8);
        pc = C[--cp];
        break;
      case 0x40: { // LOAD
        const a = D[sp - 1];
        if (a < 0 || a > 255) return done(6);
        D[sp - 1] = M[a];
        break;
      }
      case 0x41: { // STORE
        const a = D[sp - 1];
        if (a < 0 || a > 255) return done(6);
        M[a] = D[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: { // PRINT, decimal ASCII, no newline
        const bs = enc.encode(String(D[sp - 1]));
        if (ol + bs.length > OUT_LIMIT) return done(11);
        sp--;
        out.set(bs, ol);
        ol += bs.length;
        break;
      }
      case 0x51: // PUTC, one byte
        if (ol + 1 > OUT_LIMIT) return done(11);
        out[ol++] = D[--sp] & 255;
        break;
      case 0x52: // IN, -1 once the input is used up
        D[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53: // EXIT, low byte of the code
        return done(D[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const [out, code] = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), out);
  writeFileSync(join(O, id, 'exit.txt'), `${code}\n`);
}
