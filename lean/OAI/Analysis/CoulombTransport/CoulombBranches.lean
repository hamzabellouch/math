import OAI.Analysis.CoulombTransport.Model
import OAI.Analysis.CoulombTransport.LocalImplicit
import OAI.Analysis.CoulombTransport.HessianCLM

namespace OAI

noncomputable section

open scoped Topology ContDiff

namespace Problem356.CoulombBranches

open LocalImplicit LocalHessian

/-- The concrete K=20 matrix certificate discharges every invertibility premise
of the local branch theorem once the two partial derivatives are identified. -/
theorem stationary_charts_of_center_derivatives
    (G : E3 × (E3 × E3) → E3 × E3) (k : Fin 3) (p : E3) (s : E3 × E3)
    (hG : ContDiffAt ℝ ω G (p, s)) (hzero : G (p, s) = 0)
    (hstate : fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inr ℝ E3 (E3 × E3) =
      stateOperator k)
    (hparameter : fderiv ℝ G (p, s) ∘L ContinuousLinearMap.inl ℝ E3 (E3 × E3) =
      parameterOperator k) :
    Nonempty (AnalyticStationaryCharts G p s) := by
  apply nonempty_analyticStationaryCharts G p s hG hzero
  · rw [hstate]
    exact stateOperator_isInvertible k
  · unfold implicitDerivative
    rw [hstate, hparameter]
    exact central_inverse_block_isInvertible k
  · unfold implicitDerivative
    rw [hstate, hparameter]
    exact opposite_inverse_block_isInvertible k

end Problem356.CoulombBranches

end

end OAI
