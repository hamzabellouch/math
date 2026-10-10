import OAI.Analysis.IrrationalRotation.Model.OperatorProperties
import OAI.Analysis.IrrationalRotation.Analysis.ChoKoLeeComparison
import OAI.Analysis.IrrationalRotation.Operators.HilbertConsequence
import OAI.Analysis.IrrationalRotation.Rotation.RotationAlgebra
import OAI.Analysis.IrrationalRotation.Spectral.RotationQuasinilpotent

namespace OAI

noncomputable section
namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

theorem cho_ko_lee_comparison_of_continuous_circle_obstruction
    (hH : ¬ FiniteDimensional ℂ H) {θ : ℝ} (hθ : Irrational θ)
    (f : C(Circle, ℝ)) (hf : IsContinuousCircleWeight f)
    (hinv : HasOnlyTrivialInvariantProjections
      (Rotation.algebra θ) (Rotation.weightedReal θ f)) :
    ∃ Q : H →L[ℂ] H, Q ≠ 0 ∧ NormQuasinilpotent Q ∧
      HasNoNontrivialHyperinvariantSubspace Q ∧
      operatorCommutant Q ≠ ⊤ ∧ IsStronglyClosed (operatorCommutant Q) ∧
      IsTransitive (operatorCommutant Q) ∧
      operatorCommutant (1 + Q) = operatorCommutant Q ∧
      ∀ C : H → H, ∀ hC : IsConjugation C,
        IsInfiniteConjugationIsometry hC.toHilbertConjugation (1 + Q) ∧
        HasNoNontrivialHyperinvariantSubspace (1 + Q) := by
  obtain ⟨Q, hne, hQ, hhyper, hproper, hclosed, htrans⟩ :=
    transitive_commutant_of_circle_witness (F := H) hH (Rotation.algebra θ)
      (Rotation.weightedReal_mem_algebra θ f)
      (Rotation.weightedReal_ne_zero_of_isContinuousCircleWeight θ f hf)
      (Rotation.weightedReal_normQuasinilpotent hθ f hf) hinv
  refine ⟨Q, hne, hQ, hhyper, hproper, hclosed, htrans,
    operatorCommutant_one_add Q, fun C hC => ?_⟩
  exact ⟨isInfiniteConjugationIsometry_one_add_of_isConjugation hC hQ,
    (hasNoNontrivialHyperinvariantSubspace_one_add_iff Q).2 hhyper⟩

end Invariant233

end

end OAI
