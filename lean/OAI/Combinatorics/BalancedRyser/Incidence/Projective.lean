import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum
import OAI.Combinatorics.BalancedRyser.Incidence.Affine

namespace OAI

namespace Balanced

abbrev ProjectiveLine (F : Type*) := Option (Line F)

variable {F : Type*} [Field F]

def ProjectiveIncident (P : ProjectivePoint F) : ProjectiveLine F → Prop
  | some l => ThroughProjective l P
  | none => match P with
    | Sum.inl _ => False
    | Sum.inr _ => True

def dualLine : ProjectivePoint F → ProjectiveLine F
  | Sum.inl p => some (some p.1, -p.2)
  | Sum.inr none => none
  | Sum.inr (some m) => some (none, m)

def dualPoint : ProjectiveLine F → ProjectivePoint F
  | none => Sum.inr none
  | some (none, b) => Sum.inr (some b)
  | some (some m, b) => Sum.inl (m, -b)

def affineDualPoint (l : Line F) : ProjectivePoint F := dualPoint (some l)

variable [Fintype F] [DecidableEq F]

instance (P : ProjectivePoint F) (l : ProjectiveLine F) :
    Decidable (ProjectiveIncident P l) := by
  cases l with
  | some l => exact inferInstanceAs (Decidable (ThroughProjective l P))
  | none => cases P <;> simp only [ProjectiveIncident] <;> infer_instance

def missedAffine (C : Finset (Line F)) : Finset (Point F) :=
  Finset.univ.filter (fun p => ∀ l ∈ C, ¬ OnLine p l)

def missedProjective (C : Finset (Line F)) : Finset (ProjectivePoint F) :=
  Finset.univ.filter (fun P => ∀ l ∈ C, ¬ ThroughProjective l P)

def representedDirections (C : Finset (Line F)) : Finset (Direction F) :=
  C.image Prod.fst

def dualPointSet (C : Finset (Line F)) : Finset (ProjectivePoint F) :=
  C.image affineDualPoint

def skewProjective (B : Finset (ProjectivePoint F)) : Finset (ProjectiveLine F) :=
  Finset.univ.filter (fun l => ∀ P ∈ B, ¬ ProjectiveIncident P l)

end Balanced

end OAI
