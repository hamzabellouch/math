import OAI.Geometry.RCD.Coordinates.VolumeRigidityMain

namespace OAI

/-! # Bi-Lipschitz coordinates at regular noncollapsed RCD points

Harmonic coordinates, heat-kernel estimates, summable directional pinching,
and nonlinear renormalization give an open chart at every regular point.
Both chart domains and Euclidean images are open, and the metric estimates
use the restricted ambient distance.
-/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.regular_point_chart_nonpositive {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (hK : K ≤ 0)
    {p : X} (hp : IsRegular n p) : HasOpenBilipschitzChart n p := by
  let := hX.properSpace hn
  let := hX.hausdorff_regular
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  have hscalar := hX.scalarBochner_nonpositive K n hn hK p
  have hhessian := hX.poisson_hessian_input_of_scalar hn hscalar
  have haction := hX.poisson_hessian_action_input_of_scalar hn hscalar
  have hproduct := hX.poisson_gradient_product_input_of_scalar hn hscalar
  have hm := hX.measuredCoordinateInput
  have hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  have hg := hX.canonicalHeatKernel_coordinateBounds hn p
  have hpoisson := hX.poissonGradientInput hk hg hhessian
  obtain ⟨a,ha,hBG⟩ := hX.exists_model_ballVolumeComparison hn
  exact every_regular_point_has_bilipschitz_coordinates_of_flat_coordinate_heat_bounds_actual
    hn hX ha (hX.pointedRescalingPrecompactness hn p) hp
    (hX.regular_volume_convergence hn hp) (hm.euclideanMeasuredRescalingConvergence hn p)
    hBG (hX.smallScaleVolumeUpper hn ha) hX.localSquaredDistanceInput
    hX.localDirichletSobolevInput hpoisson haction hproduct (hX.localMeanPoincareInput hn)
    hX.poissonHarmonicCompactnessInput hhessian hX.harmonicMeanValueInput hX.initialSplittingInput
    (hX.transformationInput_of_measured hm) (hX.flatSplittingInput_of_measured hm)
    hhessian.harmonicBochnerInput hX.goodCutoffInput (hX.harmonicMomentCompactnessInput hn)
    (harmonicGradientInput_of_poisson_and_mean hX hpoisson hX.harmonicMeanValueInput)
    (euclideanHarmonicHessianInput (by omega)) hm hk hg
    (hX.canonicalHeatKernel_gaussian_difference hn p) (euclideanGevreyCutoffInput n)

/-- Every regular point of a noncollapsed RCD(K,n) space, n ≥ 2, has an
open neighborhood bi-Lipschitz homeomorphic to an open subset of Euclidean n. -/
theorem every_regular_point_has_bilipschitz_coordinates {K : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) {p : X} (hp : IsRegular n p) :
    HasOpenBilipschitzChart n p := by
  by_cases hK : K ≤ 0
  · exact hX.regular_point_chart_nonpositive hn hK hp
  · exact (hX.zero_of_nonneg_curvature hn (le_of_not_ge hK)).regular_point_chart_nonpositive
      hn le_rfl hp

end RegularPointCoordinates

end

end OAI
