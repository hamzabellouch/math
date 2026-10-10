import OAI.Geometry.RuledCovering.Model

namespace OAI

open Filter Topology

namespace CylinderCovering.SingularParameterRange
open RuledApproximation

structure Statement : Prop where
  negative_range : ∀ p : ℝ, 1 < p →
    (singularCoefficient p < 0 ↔ p < (Real.sqrt 51 - 5) / 2)
  critical_zero : singularCoefficient ((Real.sqrt 51 - 5) / 2) = 0
  endpoint_value : singularCoefficient 1 = -(1 / 480 : ℝ)
  endpoint_limit : Tendsto singularCoefficient (𝓝 1) (𝓝 (-(1 / 480 : ℝ)))
  cutoff_window : ∀ p : ℝ,
    (∃ γ : ℝ, 1 < γ ∧ γ < 1 / (2 - p)) ↔ 1 < p ∧ p < 2
  endpoint_degenerate : ∀ z : Plane, 0 < z 1 →
    LinearMap.det (fderiv ℝ (singularField 1) z).toLinearMap = 0 ∧
    ∀ μ : ℝ, Module.End.HasEigenvalue (fderiv ℝ (singularField 1) z).toLinearMap μ → μ = 0

end CylinderCovering.SingularParameterRange

end OAI
