import OAI.Analysis.FiniteFactor.CrossedProduct.OrderedTorusSampling
import OAI.Analysis.FiniteFactor.CrossedProduct.FreeRotation
import OAI.Analysis.FiniteFactor.CrossedProduct.PhaseCoverage
import OAI.Analysis.FiniteFactor.CrossedProduct.GeneratedAlgebra
import OAI.Analysis.FiniteFactor.CrossedProduct.HilbertSeparable
import OAI.Analysis.FiniteFactor.CrossedProduct.VacuumFunctional

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- One fixed realization supplies phases, rational independence, ordered
sampling and the actual nonzero quasinilpotent operator in its generated
algebra, before any candidate invariant projection. Factor and predual
properties are not included: they remain obligations about this algebra. -/
theorem exists_source_prepared_base : ∃ θ : SourceCoordinate → ℝ,
    SourceRationalIndependent θ ∧
    (∃ j : ℕ, SourceSecondPhasesFrom θ j) ∧
    SourceOrderedTorusSampling θ ∧
    (∀ k : ℤ, MeasurePreserving (coordinateRotate θ k) sourceSamplingHaar sourceSamplingHaar) ∧
    (∀ k : ℤ, k ≠ 0 → ∀ x, coordinateRotate θ k x ≠ x) ∧
    ∃ hθ : SourceAngles θ,
      let T := sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg
      T ∈ sourceAlgebra θ ∧ T ≠ 0 ∧ Function.Injective T ∧ ‖T‖ ≤ 1 ∧
        Tendsto (fun n : ℕ => ‖T^n‖^(1/(n : ℝ))) atTop (𝓝 0) := by
  have hall := sourceAngleLaw_admissible.and (sourceAngleLaw_rationalIndependent.and
    (sourceAngleLaw_second_phases_from.and sourceOrderedTorusSampling_event))
  obtain ⟨θ,ha,hr,hp,hs⟩ := hall.exists
  exact ⟨θ,hr,hp,hs,fun k => coordinateRotate_preserving θ k,
    fun k hk x => hr.rotation_free k hk x,ha,staged_sourceOperator_mem θ ha,
    staged_sourceOperator_properties θ ha⟩

end
end FiniteFactor

end OAI
