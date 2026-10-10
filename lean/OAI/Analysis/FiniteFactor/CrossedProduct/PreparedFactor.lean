import OAI.Analysis.FiniteFactor.CrossedProduct.PreparedErgodic
import OAI.Analysis.FiniteFactor.CrossedProduct.NoMinimalProjection

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

theorem exists_source_prepared_factor : ∃ θ : SourceCoordinate → ℝ,
    SourceRationalIndependent θ ∧
    (∃ j : ℕ, SourceSecondPhasesFrom θ j) ∧
    SourceOrderedTorusSampling θ ∧
    Ergodic (coordinateRotate θ 1) sourceBaseMeasure ∧
    HasScalarCenter (sourceAlgebra θ) ∧
    IsFiniteAlgebra (sourceAlgebra θ) ∧
    HasNoMinimalProjection (sourceAlgebra θ) ∧
    HasSeparablePredual (sourceAlgebra θ) ∧
    ∃ hθ : SourceAngles θ,
      let T := sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg
      T ∈ sourceAlgebra θ ∧ T ≠ 0 ∧ Function.Injective T ∧ ‖T‖ ≤ 1 ∧
        Tendsto (fun n : ℕ => ‖T^n‖^(1/(n : ℝ))) atTop (𝓝 0) := by
  obtain ⟨θ,hr,hphase,hs,he,hcenter,hfinite,hpredual,hT⟩ := exists_source_prepared_ergodic
  exact ⟨θ,hr,hphase,hs,he,hcenter,hfinite,sourceAlgebra_hasNoMinimalProjection θ,hpredual,hT⟩

end
end FiniteFactor

end OAI
