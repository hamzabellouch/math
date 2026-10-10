import OAI.Analysis.FiniteFactor.CrossedProduct.PreparedBase
import OAI.Analysis.FiniteFactor.CrossedProduct.TracialRepresentation

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- One actual finite tracial source algebra, with the sampled rotation and
nonzero quasinilpotent operator. Scalar center, no minimal projections,
separable predual and the invariant-projection conclusion remain separate. -/
theorem exists_source_prepared_finite : ∃ θ : SourceCoordinate → ℝ,
    SourceRationalIndependent θ ∧
    (∃ j : ℕ, SourceSecondPhasesFrom θ j) ∧
    SourceOrderedTorusSampling θ ∧
    (∀ k : ℤ, MeasurePreserving (coordinateRotate θ k) sourceSamplingHaar sourceSamplingHaar) ∧
    (∀ k : ℤ, k ≠ 0 → ∀ x, coordinateRotate θ k x ≠ x) ∧
    IsFiniteAlgebra (sourceAlgebra θ) ∧
    Nonempty (TracialRepresentation (sourceAlgebra θ)) ∧
    ∃ hθ : SourceAngles θ,
      let T := sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg
      T ∈ sourceAlgebra θ ∧ T ≠ 0 ∧ Function.Injective T ∧ ‖T‖ ≤ 1 ∧
        Tendsto (fun n : ℕ => ‖T^n‖^(1/(n : ℝ))) atTop (𝓝 0) := by
  obtain ⟨θ,hr,hp,hs,hm,hf,ho⟩ := exists_source_prepared_base
  exact ⟨θ,hr,hp,hs,hm,hf,sourceAlgebra_finite θ,⟨sourceTracialRepresentation θ⟩,ho⟩

end
end FiniteFactor

end OAI
