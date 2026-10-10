import Mathlib
import OAI.Geometry.HyperbolicGroups.StarRate
import OAI.Geometry.HyperbolicGroups.SixCounts

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate
namespace Occurrences

/-- Table types and the incidence of all seven fan slots of every top. Fans
are indexed once, including those used by more than one top. -/
abbrev Shape (s u q : ℕ) := Σ t : Fin u → Fin 7,
  (Fin s → (i : Fin 7) → {b : Fin u // t b = i}) × (Fin q → TwoPath)

abbrev Entry (A : Type*) := TableModel.Entry (A := A) rowSupport ⊕ (Fin 6 → A)

def probability (α β δ : ℝ) (A : Type*) [Fintype A] : Entry A → ℝ
  | .inl e => actualProbability α β δ A e.1
  | .inr _ => SixTable.probability (A := A) δ

lemma probability_mem {α β δ : ℝ} {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ) (e : Entry A) :
    probability α β δ A e ∈ Set.Icc (0:ℝ) 1 := by
  cases e with
  | inl e => exact actualProbability_mem ha hb hd e.1
  | inr _ => exact SixTable.probability_mem hd


end Occurrences
end IncidenceTemplate
end HyperbolicObstruction
end
end
end

end OAI
