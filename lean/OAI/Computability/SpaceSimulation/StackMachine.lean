import OAI.Computability.SpaceSimulation.Machine

namespace OAI

/-! A finite-control intermediate machine with a fixed number of stacks.
Stack alphabet binary, top at the start of the lists. We bound lengths
per stack; the fixed number of stacks makes this sufficient. -/
namespace Fifths

inductive StOp
  | keep | push (b : Bool) | pop
  deriving Fintype

namespace StOp
/-- Popping empty is allowed and does nothing. -/
def apply : StOp → List Bool → List Bool
  | keep, l => l
  | push b, l => b :: l
  | pop, l => l.tail
end StOp

structure Store (J K : Type) where
  ro : Readers J
  st : K → List Bool

structure StChange (J K : Type) where
  advance : Advances J
  ops : K → StOp

structure SAction (Q J K : Type) extends StChange J K where
  next : Q

namespace StChange
variable {J K : Type}
def none : StChange J K :=
  ⟨{}, fun _ => .keep⟩
end StChange

namespace SAction
variable {Q J K : Type}
def withState (c : StChange J K) (q : Q) : SAction Q J K := ⟨c, q⟩
def none (q : Q) : SAction Q J K := ⟨.none, q⟩
end SAction

namespace Store
variable {X J K : Type}

def init (d : K → List Bool := fun _ => []) : Store J K :=
  ⟨.home, d⟩

def see (s : Store J K) (k : K) : Option Bool :=
  (s.st k).head?

def perform (s : Store J K) (i : Inputs X J) (m : StChange J K) : Store J K :=
  ⟨s.ro.walk i m.advance, fun k => (m.ops k).apply (s.st k)⟩

@[simp] theorem stationary (s : Store J K) (i : Inputs X J) :
    s.perform i .none = s := rfl

def ok (s : Store J K) (B : ℕ) : Prop := ∀ k, (s.st k).length ≤ B

theorem ok.mono {s : Store J K} {B C} (r : s.ok B) (h : B ≤ C) : s.ok C :=
  fun k => le_trans (r k) h
end Store

/-- Usage as bounded computations will have X,J,K and Y finite. -/
structure SM (X J K Y : Type) where
  Q : Type
  [finiteQ : Finite Q]
  start : Q
  table : Q → Reads X J → (K → Option Bool) → Y ⊕ SAction Q J K
attribute [instance] SM.finiteQ

namespace SM
variable {X J K Y : Type} (M : SM X J K Y)

abbrev Cfg := M.Q × Store J K

def step (i : Inputs X J) (w : M.Cfg) : Y ⊕ M.Cfg :=
  match M.table w.1 (w.2.ro.see i) w.2.see with
  | Sum.inl y => .inl y
  | Sum.inr a => .inr (a.next, w.2.perform i a.toStChange)

/-- Auxiliary runs at any program counter. -/
abbrev Run (i : Inputs X J) (B : ℕ) : M.Cfg → M.Cfg → Y → Prop :=
  Runs (M.step i) (fun w => w.2.ok B)

def Exec (i : Inputs X J) (B : ℕ) (s t : Store J K) (y : Y) : Prop :=
  ∃ q, M.Run i B (M.start, s) (q, t) y

namespace Exec
variable {M} {i B} {s t : Store J K} {y : Y}
theorem startOk (e : M.Exec i B s t y) : s.ok B := by
  obtain ⟨q, e⟩ := e
  exact e.startOk

theorem endOk (e : M.Exec i B s t y) : t.ok B := by
  obtain ⟨q, e⟩ := e
  exact e.endOk

theorem mono {B'} (e : M.Exec i B s t y) (h : B ≤ B') : M.Exec i B' s t y := by
  obtain ⟨q, e⟩ := e
  exact ⟨q, e.mono fun _ a => a.mono h⟩

theorem unique {B' u v} (e : M.Exec i B s t y) (e' : M.Exec i B' s u v) :
    (t, y) = (u, v) := by
  obtain ⟨q, e⟩ := e
  obtain ⟨q', e'⟩ := e'
  exact congrArg (fun w => (w.1.2, w.2)) (e.unique e')
end Exec
end SM
end Fifths

end OAI
