import Mathlib

namespace OAI

/-! Finite-machine statements of the capped and unknown-time one-writable-tape
simulation theorem. Work space counts the bits in every visited writable cell;
public endmarked input tapes are read-only. -/

namespace Fifths

inductive Dir
  | L | N | R
  deriving DecidableEq

instance : Fintype Dir := ⟨{.L, .N, .R}, by intro d; cases d <;> simp⟩

namespace Dir
@[simp] def delta : Dir → ℤ
  | L => -1
  | N => 0
  | R => 1
end Dir

inductive Mark (A : Type)
  | left
  | sym (a : A)
  | right
  deriving DecidableEq, Fintype

namespace Mark
variable {A : Type}
def see (w : List A) : ℕ → Mark A
  | 0 => left
  | p+1 =>
    match w[p]? with
    | some a => sym a
    | none => right

def walk (w : List A) (p : ℕ) : Dir → ℕ
  | .N => p
  | .L => p - 1
  | .R => if w.length < p then p else p + 1
end Mark

inductive Runs {σ Y : Type} (f : σ → Y ⊕ σ) (P : σ → Prop) :
    σ → σ → Y → Prop
  | stop {s y} (ok : P s) (eqn : f s = Sum.inl y) : Runs f P s s y
  | step {s s' t y} (ok : P s) (eqn : f s = Sum.inr s')
      (tail : Runs f P s' t y) : Runs f P s t y

structure Inputs (X J : Type) where
  publicWord : List X
  arg : J → List Bool

structure Readers (J : Type) where
  px : ℕ := 0
  parg : J → ℕ := fun _ => 0

structure Reads (X J : Type) where
  sx : Mark X
  sarg : J → Mark Bool

structure Advances (J : Type) where
  dx : Dir := .N
  darg : J → Dir := fun _ => .N

namespace Readers
variable {X J : Type}
def home : Readers J := {}
def see (r : Readers J) (i : Inputs X J) : Reads X J :=
  ⟨Mark.see i.publicWord r.px, fun j => Mark.see (i.arg j) (r.parg j)⟩
def walk (r : Readers J) (i : Inputs X J) (a : Advances J) : Readers J :=
  ⟨Mark.walk i.publicWord r.px a.dx, fun j => Mark.walk (i.arg j) (r.parg j) (a.darg j)⟩
end Readers

structure Tape (A : Type) where
  pos : ℤ
  sym : ℤ → A

structure WriteMove (A : Type) where
  sym : A
  dir : Dir

namespace Tape
variable {A : Type}
def init (a : A) : Tape A := ⟨0, fun _ => a⟩
def see (w : Tape A) : A := w.sym w.pos
def perform (w : Tape A) (m : WriteMove A) : Tape A :=
  ⟨w.pos + m.dir.delta, Function.update w.sym w.pos m.sym⟩
end Tape

structure TAction (Q J K : Type) (W : K → Type) where
  next : Q
  advance : Advances J
  moves : ∀ k : K, WriteMove (W k)

structure TM (X J Y : Type) where
  Q : Type
  [finiteQ : Finite Q]
  K : Type
  [tapes : Fintype K]
  W : K → Type
  [symbols : ∀ k, Fintype (W k)]
  blank : ∀ k, W k
  start : Q
  table : Q → Reads X J → ((k : K) → W k) → Y ⊕ TAction Q J K W

attribute [instance] TM.finiteQ TM.tapes TM.symbols

namespace TM
variable {X J Y : Type} (M : TM X J Y)

structure Cfg where
  state : M.Q
  ro : Readers J
  work : ∀ k, Tape (M.W k)

def initial : M.Cfg :=
  ⟨M.start, .home, fun k => .init (M.blank k)⟩

def step (i : Inputs X J) (s : M.Cfg) : Y ⊕ M.Cfg :=
  match M.table s.state (s.ro.see i) (fun k => (s.work k).see) with
  | Sum.inl y => .inl y
  | Sum.inr a =>
    .inr ⟨a.next, s.ro.walk i a.advance, fun k => (s.work k).perform (a.moves k)⟩

structure Window where
  l : M.K → ℕ
  h : M.K → ℕ

def width (k : M.K) : ℕ := max 1 (Fintype.card (M.W k) - 1).size

namespace Window
variable {M}
def ok (w : M.Window) (s : M.Cfg) : Prop :=
  ∀ k, -(w.l k : ℤ) ≤ (s.work k).pos ∧ (s.work k).pos ≤ (w.h k : ℤ)
open BigOperators
def bits (w : M.Window) : ℕ :=
  ∑ k, (w.l k + w.h k + 1) * M.width k
end Window

def Within (i : Inputs X J) (y : Y) (S : ℕ) : Prop :=
  ∃ w : M.Window, w.bits ≤ S ∧ ∃ t, Runs (M.step i) w.ok M.initial t y
end TM

end Fifths

namespace Fifths

structure SingleAct (Q A : Type) (r : ℕ) where
  out : Q
  write : WriteMove A
  others : Fin r → Dir

structure Single (X : Type) where
  Q : Type
  [states : Fintype Q]
  A : Type
  [symbols : Fintype A]
  beginState : Q
  halted : Q → Bool
  heads : ℕ
  program : Q → A → (Fin heads → A) → SingleAct Q A heads
  sensor : List X → Option (Fin heads) → ℤ → A

attribute [instance] Single.states Single.symbols

namespace Single
variable {X : Type} (M : Single X)
instance : Nonempty M.A := ⟨M.sensor [] none 0⟩
instance : Nonempty M.Q := ⟨M.beginState⟩
abbrev Tag := Option (Fin M.heads)

structure At where
  state : M.Q
  tape : Tape M.A
  ro : Fin M.heads → ℤ

def move (q : M.Q) (s : M.A) (r : Fin M.heads → M.A) :
    SingleAct M.Q M.A M.heads :=
  if M.halted q then
    ⟨q,⟨s,.N⟩,fun _ => .N⟩
  else M.program q s r

def initial (x : List X) : M.At :=
  ⟨M.beginState,⟨0,M.sensor x none⟩, fun _ => 0⟩

def next (x : List X) (s : M.At) : M.At :=
  let t := M.move s.state s.tape.see (fun i => M.sensor x (some i) (s.ro i))
  ⟨t.out,s.tape.perform t.write,fun i => s.ro i + (t.others i).delta⟩

def atTime (M : Single X) (x : List X) : ℕ → M.At :=
  Nat.rec (M.initial x) (fun _ s => M.next x s)

abbrev Outcome := M.Q × Bool
def finish (q : M.Q) : M.Outcome :=
  (q, M.halted q)
def outcome (x : List X) (n : ℕ) : M.Outcome :=
  M.finish (M.atTime x n).state

def Inside (t : ℕ) (q : ℤ) : Prop := -(t:ℤ) ≤ q ∧ q ≤ (t:ℤ)
end Single

end Fifths

namespace Fifths

namespace Entry
noncomputable def code {A : Type} [Fintype A] (a : A) : ℕ :=
  (Fintype.equivFin A a).val
end Entry

def binaryIn {X J : Type} (pub : List X) (f : J → ℕ) : Inputs X J :=
  ⟨pub, fun j => (f j).bits⟩

def files {X : Type} (x : List X) : Inputs X Empty :=
  ⟨x, Empty.elim⟩

namespace Single
open Entry
variable {X : Type} (M : Single X)

inductive Arg
  | cap | tag | minus | magnitude
  deriving DecidableEq

instance : Fintype Arg :=
  ⟨{.cap, .tag, .minus, .magnitude}, by intro a; cases a <;> simp⟩
abbrev Sym := TM X Arg M.A

noncomputable def arg (T : ℕ) (h : M.Tag) (p : ℤ) : Arg → ℕ
  | .cap => T
  | .tag => code h
  | .minus => (decide (p < 0)).toNat
  | .magnitude => p.natAbs
end Single

namespace Cost
noncomputable def Log (T : ℕ) := Real.log (T+2 : ℝ) / Real.log 2
noncomputable def exponent := (2:ℝ)/5
end Cost

namespace Single
open Cost
variable {X : Type} (M : Single X)
def Access (A : M.Sym) (p q : ℝ) (x : List X) (T : ℕ) : Prop :=
  ∀ (h : M.Tag) (l : ℤ), Inside T l →
    ∃ s : ℕ, (s:ℝ) ≤ p * (Log T)^q ∧
      A.Within (binaryIn x (M.arg T h l)) (M.sensor x h l) s
end Single

end Fifths

namespace Fifths.Single
open Entry Cost
variable {X : Type} (M : Single X)

theorem capped [Fintype X] (A : M.Sym) (p q : ℝ) (hp : 1 ≤ p) (_hq : 1 ≤ q) :
    ∃ (N : TM X Unit M.Outcome) (e : ℕ) (c : ℝ), 0 < c ∧
      ∀ (x : List X) (T : ℕ), 2 ≤ T → M.Access A p q x T →
        ∃ b : ℕ, N.Within (binaryIn x (fun _ => T)) (M.outcome x T) b ∧
          (b:ℝ) ≤ c*(T:ℝ)^exponent*(Log T)^e := by
  sorry

theorem unknown [Fintype X] (A : M.Sym) (p q : ℝ) (hp : 1 ≤ p) (_hq : 1 ≤ q) :
    ∃ (N : TM X Empty M.Outcome) (e : ℕ) (c : ℝ), 0 < c ∧
      ∀ (x : List X), (∀ T, 2 ≤ T → M.Access A p q x T) →
        ∀ (t : ℕ), (M.outcome x t).2 = true →
          ∃ b, N.Within (files x) (M.outcome x t) b ∧
            (b:ℝ) ≤ c*((t:ℝ)+2)^exponent*(Log t)^e := by
  sorry

end Fifths.Single

end OAI
