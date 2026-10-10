import OAI.Analysis.FiniteFactor.CrossedProduct.PreparedFinite
import OAI.Analysis.FiniteFactor.CrossedProduct.ScalarCenter
import OAI.Analysis.FiniteFactor.CrossedProduct.PredualIdentification
import OAI.Analysis.FiniteFactor.CrossedProduct.InvariantConull

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

/-- The actual source construction now includes proved ergodicity, scalar center,
finiteness and the exact separable predual. No minimal-projection or arbitrary
invariant-projection conclusion is asserted here. -/
theorem exists_source_prepared_ergodic : ∃ θ : SourceCoordinate → ℝ,
    SourceRationalIndependent θ ∧
    (∃ j : ℕ, SourceSecondPhasesFrom θ j) ∧
    SourceOrderedTorusSampling θ ∧
    Ergodic (coordinateRotate θ 1) sourceBaseMeasure ∧
    HasScalarCenter (sourceAlgebra θ) ∧
    IsFiniteAlgebra (sourceAlgebra θ) ∧
    HasSeparablePredual (sourceAlgebra θ) ∧
    ∃ hθ : SourceAngles θ,
      let T := sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg
      T ∈ sourceAlgebra θ ∧ T ≠ 0 ∧ Function.Injective T ∧ ‖T‖ ≤ 1 ∧
        Tendsto (fun n : ℕ => ‖T^n‖^(1/(n : ℝ))) atTop (𝓝 0) := by
  obtain ⟨θ,hr,hphase,hs,_hm,_hfree,hfinite,_htrace,hT⟩ := exists_source_prepared_finite
  exact ⟨θ,hr,hphase,hs,coordinateRotate_ergodic θ hr,sourceAlgebra_hasScalarCenter θ hr,
    hfinite,sourceAlgebra_hasSeparablePredual θ,hT⟩

end
end FiniteFactor

end OAI
