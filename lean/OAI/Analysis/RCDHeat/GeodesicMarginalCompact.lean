import Mathlib
import OAI.Analysis.RCDHeat.CDSubplan
import OAI.Analysis.RCDHeat.CompactKantorovich
import OAI.Analysis.RCDHeat.SobolevTestPlan

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: GeodesicMarginalCompact. -/



open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [ProperSpace X]
  [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 

 theorem isCompact_bounded_geodesic_plans_marginals (p : X) {R : ℝ} (hR : 0 ≤ R)
    (ν₀ ν₁ : ProbabilityMeasure X) :
    IsCompact {π : ProbabilityMeasure C(Time,X) |
      (∀ᵐ γ ∂(π : Measure C(Time,X)), IsGeodesic γ ∧ ∀ t, dist (γ t) p ≤ R) ∧
      π.map (fun γ => γ 0) = ν₀ ∧
      π.map (fun γ => γ 1) = ν₁} := by
  have h0 : Continuous (fun π : ProbabilityMeasure C(Time,X) =>
      π.map (fun γ => γ 0)) :=
    ProbabilityMeasure.continuous_map (continuous_eval_const 0)
  have h1 : Continuous (fun π : ProbabilityMeasure C(Time,X) =>
      π.map (fun γ => γ 1)) :=
    ProbabilityMeasure.continuous_map (continuous_eval_const 1)
  exact (isCompact_bounded_geodesic_plans p hR).inter_right
    ((isClosed_eq h0 continuous_const).inter (isClosed_eq h1 continuous_const))
end RegularPointCoordinates

end OAI
