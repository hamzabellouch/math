import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

namespace OAI

namespace Balanced

abbrev Point (F : Type*) := F × F
abbrev Direction (F : Type*) := Option F
abbrev Line (F : Type*) := Direction F × F
abbrev ProjectivePoint (F : Type*) := Point F ⊕ Direction F

variable {F : Type*} [Field F]

def lineEval : Direction F → Point F → F
  | none, p => p.1
  | some m, p => p.2 - m * p.1

def OnLine (p : Point F) (l : Line F) : Prop := lineEval l.1 p = l.2

def lineThrough (d : Direction F) (p : Point F) : Line F := (d, lineEval d p)

def ThroughProjective (l : Line F) : ProjectivePoint F → Prop
  | Sum.inl p => OnLine p l
  | Sum.inr d => l.1 = d

def joiningLine [DecidableEq F] (p r : Point F) : Line F :=
  if p.1 = r.1 then (none, p.1)
  else let m := (r.2 - p.2) / (r.1 - p.1)
       (some m, p.2 - m * p.1)

def lineIntersection (l m : Line F) : Point F :=
  match l.1, m.1 with
  | none, none => (l.2, 0)
  | none, some b => (l.2, b * l.2 + m.2)
  | some a, none => (m.2, a * m.2 + l.2)
  | some a, some b =>
      let x := (m.2 - l.2) / (a - b)
      (x, a * x + l.2)

variable [Fintype F] [DecidableEq F]

instance (p : Point F) (l : Line F) : Decidable (OnLine p l) :=
  inferInstanceAs (Decidable (lineEval l.1 p = l.2))

instance (l : Line F) (P : ProjectivePoint F) : Decidable (ThroughProjective l P) :=
  match P with
  | Sum.inl p => inferInstanceAs (Decidable (OnLine p l))
  | Sum.inr d => inferInstanceAs (Decidable (l.1 = d))

def linePoints (l : Line F) : Finset (Point F) := Finset.univ.filter (fun p => OnLine p l)

def linesInDirection (d : Direction F) : Finset (Line F) :=
  Finset.univ.filter (fun l => l.1 = d)

def CoversPoints (C : Finset (Line F)) (U : Finset (Point F)) : Prop :=
  ∀ p ∈ U, ∃ l ∈ C, OnLine p l

end Balanced

end OAI
