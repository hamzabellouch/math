import OAI.Analysis.CoulombTransport.Model
import OAI.Analysis.CoulombTransport.LocalImplicit
import OAI.Analysis.CoulombTransport.StationaryEquation
import OAI.Analysis.CoulombTransport.HessianMatrix

namespace OAI

noncomputable section
open scoped ContDiff

namespace Problem356.CoulombCharts

open CoulombCalculus GeometryJets LocalImplicit

/-- The computed state derivative is the coercive, invertible operator certified
by the finite-dimensional algebra, in the actual product-space coordinates. -/
theorem centerStateHessian_axis_eq (k : Fin 3) :
    centerStateHessian 20 (CoulombCalculus.pairHessian (axisVector k)) =
      LocalHessian.stateOperator k := by
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · ext i
    simp [centerStateHessian, LocalHessian.stateOperator_fst_apply,
      pairHessian_axisVector_apply]
    ring
  · ext i
    simp [centerStateHessian, LocalHessian.stateOperator_snd_apply,
      pairHessian_axisVector_apply]
    ring

/-- The computed parameter derivative agrees with the mixed Hessian block. -/
theorem centerParameterDerivative_axis_eq (k : Fin 3) :
    centerParameterDerivative (CoulombCalculus.pairHessian (axisVector k)) =
      LocalHessian.parameterOperator k := by
  rw [pairHessian_axisVector]
  unfold centerParameterDerivative LocalHessian.parameterOperator
  dsimp
  congr 1
  module

theorem stationary_state_partial_eq (k : Fin 3) :
    fderiv ℝ (stationaryEquation 20 (axisVector k))
        (axisVector k, (0, -axisVector k)) ∘L
      ContinuousLinearMap.inr ℝ E3 (E3 × E3) = LocalHessian.stateOperator k := by
  rw [(hasFDerivAt_stationary_center 20 (axisVector k) (norm_axisVector k)).fderiv]
  have h : centerTotalDerivative 20 (CoulombCalculus.pairHessian (axisVector k)) ∘L
      ContinuousLinearMap.inr ℝ E3 (E3 × E3) =
      centerStateHessian 20 (CoulombCalculus.pairHessian (axisVector k)) := by
    apply ContinuousLinearMap.ext
    intro v
    simp [centerTotalDerivative]
  rw [h, centerStateHessian_axis_eq]

/-- Identification of the actual partial parameter derivative. -/
theorem stationary_parameter_partial_eq (k : Fin 3) :
    fderiv ℝ (stationaryEquation 20 (axisVector k))
        (axisVector k, (0, -axisVector k)) ∘L
      ContinuousLinearMap.inl ℝ E3 (E3 × E3) = LocalHessian.parameterOperator k := by
  rw [(hasFDerivAt_stationary_center 20 (axisVector k) (norm_axisVector k)).fderiv]
  have h : centerTotalDerivative 20 (CoulombCalculus.pairHessian (axisVector k)) ∘L
      ContinuousLinearMap.inl ℝ E3 (E3 × E3) =
      centerParameterDerivative (CoulombCalculus.pairHessian (axisVector k)) := by
    apply ContinuousLinearMap.ext
    intro v
    simp [centerTotalDerivative]
  rw [h, centerParameterDerivative_axis_eq]

/-- Nonlinear local Coulomb branches exist at every coordinate-axis reference triple.
Both branch coordinates are analytic local diffeomorphisms on one common source. -/
theorem nonempty_coulombCharts (k : Fin 3) :
    Nonempty (AnalyticStationaryCharts
      (stationaryEquation 20 (axisVector k)) (axisVector k) (0, -axisVector k)) := by
  apply nonempty_analyticStationaryCharts
  · exact contDiffAt_stationaryEquation_center 20 (axisVector k) (norm_axisVector k)
  · exact stationaryEquation_center 20 (axisVector k) (norm_axisVector k)
  · rw [stationary_state_partial_eq]
    exact LocalHessian.stateOperator_isInvertible k
  · unfold implicitDerivative
    rw [stationary_state_partial_eq, stationary_parameter_partial_eq]
    exact LocalHessian.central_inverse_block_isInvertible k
  · unfold implicitDerivative
    rw [stationary_state_partial_eq, stationary_parameter_partial_eq]
    exact LocalHessian.opposite_inverse_block_isInvertible k

end Problem356.CoulombCharts

end

end OAI
