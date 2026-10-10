import OAI.Analysis.IrrationalRotation.Operators.Commutant
import OAI.Analysis.IrrationalRotation.Operators.CommutantProper

namespace OAI

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem commutant_algebra_properties (T : H →L[ℂ] H)
    (hT : ¬ ∃ c : ℂ, T = c • (1 : H →L[ℂ] H)) :
    operatorCommutant T ≠ ⊤ ∧ IsStronglyClosed (operatorCommutant T) ∧
      (IsTransitive (operatorCommutant T) ↔ HasNoNontrivialHyperinvariantSubspace T) := by
  exact ⟨centralizer_singleton_ne_top_of_nonscalar T hT,
    operatorCommutant_stronglyClosed T, operatorCommutant_transitive_iff T⟩

theorem operatorCommutant_one_add (T : H →L[ℂ] H) :
    operatorCommutant (1 + T) = operatorCommutant T :=
  centralizer_singleton_one_add T

theorem isHyperinvariant_one_add_iff (T : H →L[ℂ] H) (L : Submodule ℂ H) :
    IsHyperinvariant (1 + T) L ↔ IsHyperinvariant T L := by
  unfold IsHyperinvariant
  rw [operatorCommutant_one_add]

theorem hasNoNontrivialHyperinvariantSubspace_one_add_iff (T : H →L[ℂ] H) :
    HasNoNontrivialHyperinvariantSubspace (1 + T) ↔
      HasNoNontrivialHyperinvariantSubspace T := by
  simp only [HasNoNontrivialHyperinvariantSubspace, isHyperinvariant_one_add_iff]

end Invariant233

end OAI
