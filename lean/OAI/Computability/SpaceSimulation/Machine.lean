import Mathlib

namespace OAI

/-!
Finite table machines for the result.  X is the public input alphabet (all
uses for machines as space bounds have finite types); J indexes a fixed
number of other read-only tapes, on a binary alphabet.  Each read-only tape
is endmarked and has one confined head.  Work tapes for the simulator and
accessor are two-way, with unit moves. Terminal output in a finite set
may be specified in the transition table (equivalently transition to the
associated halt state). TM transitions with writes write before moving.

Space convention is visited work cells (including the origin of each work
tape), weighted by bits/symbol in the fixed alphabets, excluding read-only
tapes. Since visited sets are intervals, we use a window certificate including
all head positions during the run.
-/

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

theorem bounds (d : Dir) : -1 ≤ d.delta ∧ d.delta ≤ 1 := by
  cases d <;> simp
end Dir

/-- Left endmarker at 0, then the word, then right endmarker. -/
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

@[simp] theorem see_zero (w : List A) : see w 0 = left := rfl
@[simp] theorem see_left (w : List A) (p) : see w p = left ↔ p = 0 := by
  cases p with
  | zero => simp
  | succ p => cases e : w[p]? <;> simp [see, e]

@[simp] theorem see_right (w : List A) (p) : see w p = right ↔ w.length < p := by
  cases p with
  | zero => simp
  | succ p =>
    by_cases h : p < w.length
    · simp [see, h, Nat.not_lt.mpr (Nat.succ_le_of_lt h)]
    · simp only [see, getElem?_neg w p h, true_iff]
      omega

def walk (w : List A) (p : ℕ) : Dir → ℕ
  | .N => p
  | .L => p - 1
  | .R => if w.length < p then p else p + 1

theorem walk_bound (w : List A) (p : ℕ) (d : Dir) (h : p ≤ w.length + 1) :
    walk w p d ≤ w.length + 1 := by
  cases d
  · simp only [walk]
    omega
  · exact h
  · simp only [walk]
    split <;> omega

end Mark

/-- Deterministic halting runs. `f s = inl y` means the transition
specifies halt with that label (no more working moves). `P` holds
also at that final configuration. -/
inductive Runs {σ Y : Type} (f : σ → Y ⊕ σ) (P : σ → Prop) :
    σ → σ → Y → Prop
  | stop {s y} (ok : P s) (eqn : f s = Sum.inl y) : Runs f P s s y
  | step {s s' t y} (ok : P s) (eqn : f s = Sum.inr s')
      (tail : Runs f P s' t y) : Runs f P s t y

namespace Runs
variable {σ Y : Type} {f : σ → Y ⊕ σ} {P Q : σ → Prop} {s t : σ} {y : Y}
theorem mono (h : ∀ z, P z → Q z) (r : Runs f P s t y) : Runs f Q s t y := by
  induction r with
  | stop o e => exact .stop (h _ o) e
  | step o e r ih => exact .step (h _ o) e ih

theorem startOk (r : Runs f P s t y) : P s := by cases r <;> assumption
theorem endOk (r : Runs f P s t y) : P t := by induction r <;> assumption
theorem endStop (r : Runs f P s t y) : f t = Sum.inl y := by induction r <;> assumption

theorem unique (r : Runs f P s t y) {u v} (r' : Runs f Q s u v) : (t, y) = (u, v) := by
  induction r generalizing u v with
  | stop o e =>
    cases r' with
    | stop _ e' =>
      rw [e] at e'
      congr
      injection e'
    | step _ e' _ => rw [e] at e'; contradiction
  | step _ e _ ih =>
    cases r' with
    | stop _ e' => rw [e] at e'; contradiction
    | step _ e' tail =>
      rw [e] at e'
      obtain rfl : _ = _ := Sum.inr.inj e'
      exact ih tail
end Runs

/-- Common read-only inputs. -/
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

@[simp] theorem stationary (r : Readers J) (i : Inputs X J) : r.walk i {} = r := rfl
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

/-- Finiteness of X, J and Y supplied in main theorem. Finite functions
in the table present no uniformity issue; all are fixed for the machine. -/
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

/-- Per tape visited positions contained in [-l,h], both nonnegative. -/
structure Window where
  l : M.K → ℕ
  h : M.K → ℕ

/-- Bits per symbol (at least one). -/
def width (k : M.K) : ℕ := max 1 (Fintype.card (M.W k) - 1).size

theorem width_pos (k : M.K) : 0 < M.width k :=
  Nat.succ_le_iff.mp (le_max_left ..)

namespace Window
variable {M}

def ok (w : M.Window) (s : M.Cfg) : Prop :=
  ∀ k, -(w.l k : ℤ) ≤ (s.work k).pos ∧ (s.work k).pos ≤ (w.h k : ℤ)

open BigOperators

def bits (w : M.Window) : ℕ :=
  ∑ k, (w.l k + w.h k + 1) * M.width k

theorem span_le (w : M.Window) (k : M.K) : w.l k + w.h k + 1 ≤ w.bits := calc
  _ ≤ (w.l k + w.h k + 1) * M.width k :=
    Nat.le_mul_of_pos_right _ (M.width_pos k)
  _ ≤ w.bits :=
    Finset.single_le_sum (f := fun k => (w.l k + w.h k + 1) * M.width k)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
end Window

/-- `M` outputs `y` using at most `S` bits. -/
def Within (i : Inputs X J) (y : Y) (S : ℕ) : Prop :=
  ∃ w : M.Window, w.bits ≤ S ∧ ∃ t, Runs (M.step i) w.ok M.initial t y

theorem Within.mono {M : TM X J Y} {i y S R} (r : M.Within i y S) (h : S ≤ R) :
    M.Within i y R := by
  obtain ⟨w, hw, g⟩ := r
  exact ⟨w, hw.trans h, g⟩

theorem Within.unique {M : TM X J Y} {i y S z R} (r : M.Within i y S)
    (g : M.Within i z R) : y = z := by
  obtain ⟨_, -, _, r⟩ := r
  obtain ⟨_, -, _, g⟩ := g
  exact congrArg Prod.snd (r.unique g)
end TM

end Fifths

end OAI
