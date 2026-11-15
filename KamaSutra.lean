/-!
# The Kama Sutra language is Turing complete

(Lean 4, core only, no Mathlib.)

A *book* is not a model of computation, so we formalise the language
**KS** whose whole alphabet is the four syllables  ka · ma · su · tra,
with every instruction a PAIR of syllables.  We then prove that KS can
simulate Böhm's P'' (a tape machine with `>`, `<`, `+`, `-` and `while`),
which is Turing complete (Böhm 1964; Minsky counter machines).
Hence KS is Turing complete.
-/

namespace KamaSutra

/-! ## 1. The four syllables and the pair encoding -/

inductive Syl | ka | ma | su | tra
  deriving DecidableEq, Repr

open Syl

abbrev Pair := Syl × Syl

/-- The four primitive tape operations. -/
inductive Op | right | left | inc | dec
  deriving DecidableEq, Repr

/-- Each operation is spelled with two syllables. -/
def enc : Op → Pair
  | .right => (ka, ka)
  | .left  => (ka, ma)
  | .inc   => (ka, su)
  | .dec   => (ka, tra)

/-- Reading a pair back (pairs starting with ma/su/tra are unused). -/
def dec? : Pair → Option Op
  | (ka, ka)  => some .right
  | (ka, ma)  => some .left
  | (ka, su)  => some .inc
  | (ka, tra) => some .dec
  | _         => none

theorem dec_enc (o : Op) : dec? (enc o) = some o := by
  cases o <;> rfl

theorem enc_injective : ∀ a b : Op, enc a = enc b → a = b := by
  intro a b h
  have := congrArg dec? h
  rw [dec_enc, dec_enc] at this
  exact Option.some.inj this

/-! ## 2. An unbounded tape and the meaning of each operation -/

structure Tape where
  left  : List Nat
  cur   : Nat
  right : List Nat

def Tape.empty : Tape := ⟨[], 0, []⟩

def Tape.goRight : Tape → Tape
  | ⟨l, c, []⟩      => ⟨c :: l, 0, []⟩
  | ⟨l, c, x :: r⟩  => ⟨c :: l, x, r⟩

def Tape.goLeft : Tape → Tape
  | ⟨[], c, r⟩      => ⟨[], 0, c :: r⟩
  | ⟨x :: l, c, r⟩  => ⟨l, x, c :: r⟩

def Op.run : Op → Tape → Tape
  | .right, t => t.goRight
  | .left,  t => t.goLeft
  | .inc,   t => { t with cur := t.cur + 1 }
  | .dec,   t => { t with cur := t.cur - 1 }

/-- Meaning of a syllable pair: its operation, or "do nothing" if unused. -/
def Pair.run (p : Pair) (t : Tape) : Tape :=
  match dec? p with
  | some o => o.run t
  | none   => t

theorem Pair.run_enc (o : Op) (t : Tape) : (enc o).run t = o.run t := by
  simp [Pair.run, dec_enc]

/-! ## 3. Programs with `while` loops, generic in the instruction alphabet -/

/-- `op a rest` = do `a`, then `rest`;  `loop body rest` = `[body]` then `rest`. -/
inductive Prog (α : Type) where
  | skip : Prog α
  | op   : α → Prog α → Prog α
  | loop : Prog α → Prog α → Prog α

/-- Big-step semantics, parametrised by what each instruction does. -/
inductive Eval {α : Type} (sem : α → Tape → Tape) : Prog α → Tape → Tape → Prop
  | skip {t} : Eval sem .skip t t
  | op {a p t t'} : Eval sem p (sem a t) t' → Eval sem (.op a p) t t'
  | loopExit {b p t t'} :
      t.cur = 0 → Eval sem p t t' → Eval sem (.loop b p) t t'
  | loopStep {b p t t₁ t'} :
      t.cur ≠ 0 → Eval sem b t t₁ → Eval sem (.loop b p) t₁ t' →
      Eval sem (.loop b p) t t'

def Prog.map {α β : Type} (f : α → β) : Prog α → Prog β
  | .skip     => .skip
  | .op a p   => .op (f a) (p.map f)
  | .loop b p => .loop (b.map f) (p.map f)

/-- Renaming instructions preserves meaning, provided the renaming does. -/
theorem eval_map {α β : Type} (f : α → β) (s : α → Tape → Tape)
    (s' : β → Tape → Tape) (h : ∀ a t, s' (f a) t = s a t) :
    ∀ {p : Prog α} {t t' : Tape},
      Eval s p t t' ↔ Eval s' (p.map f) t t' := by
  intro p t t'
  constructor
  · intro e
    induction e with
    | skip => exact .skip
    | op _ ih => exact .op (by rw [h]; exact ih)
    | loopExit hc _ ih => exact .loopExit hc ih
    | loopStep hc _ _ ih1 ih2 => exact .loopStep hc ih1 ih2
  · intro e
    generalize hq : p.map f = q at e
    induction e generalizing p with
    | skip =>
        cases p <;> simp [Prog.map] at hq
        exact .skip
    | op _ ih =>
        cases p with
        | skip => simp [Prog.map] at hq
        | loop _ _ => simp [Prog.map] at hq
        | op a1 p1 =>
            simp [Prog.map] at hq
            obtain ⟨rfl, rfl⟩ := hq
            have key := ih (p := p1) rfl
            rw [h] at key
            exact .op key
    | loopExit hc _ ih =>
        cases p <;> simp [Prog.map] at hq
        obtain ⟨rfl, rfl⟩ := hq
        exact .loopExit hc (ih rfl)
    | loopStep hc _ _ ih1 ih2 =>
        cases p <;> simp [Prog.map] at hq
        obtain ⟨rfl, rfl⟩ := hq
        exact .loopStep hc (ih1 rfl) (ih2 rfl)

/-! ## 4. The main theorem -/

/-- Böhm's language P'': loops over the four plain tape operations. -/
abbrev Bohm := Prog Op

/-- The Kama Sutra language: loops over syllable pairs. -/
abbrev KS := Prog Pair

/-- Translate any P'' program into ka-ma-su-tra. -/
def toKS (p : Bohm) : KS := p.map enc

/-- Every P'' program has a KS program with exactly the same input/output
behaviour on every tape (and vice versa). -/
theorem toKS_correct (p : Bohm) (t t' : Tape) :
    Eval Op.run p t t' ↔ Eval Pair.run (toKS p) t t' :=
  eval_map enc Op.run Pair.run Pair.run_enc

/-- **KS simulates P''.**  Since P'' is Turing complete (Böhm 1964), so is
the ka-ma-su-tra language. -/
theorem kamasutra_turing_complete :
    ∀ p : Bohm, ∃ k : KS, ∀ t t', Eval Op.run p t t' ↔ Eval Pair.run k t t' :=
  fun p => ⟨toKS p, toKS_correct p⟩

/-! ## 5. Sanity checks -/

/-- Only the 4 syllables exist; 16 pairs; exactly 4 are used by this core. -/
def allSyl : List Syl := [ka, ma, su, tra]
def allPairs : List Pair := allSyl.flatMap fun a => allSyl.map fun b => (a, b)

example : allPairs.length = 16 := by decide
example : (allPairs.filter fun p => (dec? p).isSome).length = 4 := by decide

/-- Tiny example: `ka-su ka-su` (inc, inc) leaves 2 in the first cell. -/
example : Eval Pair.run (.op (ka, su) (.op (ka, su) .skip)) Tape.empty
    ⟨[], 2, []⟩ :=
  .op (.op .skip)

end KamaSutra
