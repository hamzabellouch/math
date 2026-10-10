import OAI.Geometry.RCD.Sobolev.PublishedInputDischarge
import OAI.Geometry.RCD.Sobolev.PoissonHessianFromScalar
import OAI.Geometry.RCD.Sobolev.PoissonActionFromScalar
import OAI.Geometry.RCD.Sobolev.PoissonGradientFromScalar

namespace OAI

/-! # The chart theorem under a scalar second-order estimate

The scalar finite-dimensional Bochner inequality implies the local
second-order estimates required for the coordinate construction.
-/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem regular_coordinates_of_scalar_bochner {K : ℝ} {n : ℕ}
    (hn : 2≤n) (hX : NoncollapsedRCD K n X) :
    let _ := hX.properSpace hn
    ∀ {p : X}, IsRegular n p →
      EuclideanRescalingVolumeConvergence (hausdorff n X) n p (euclideanUnitVolume n) →
      ScalarDimensionalBochner (hausdorff n X) hX.quadratic K n →
      LocalPoissonHarmonicCompactnessInput hX →
      LocalInitialSplittingInput hX → LocalTransformationInput hX →
      LocalFlatSplittingInput hX → LocalVolumeRigidityInput hX →
      LocalHarmonicMomentCompactnessInput hX → LocalMeasuredCoordinateInput hX →
      HasOpenBilipschitzChart n p := by
  let := hX.properSpace hn
  dsimp only
  intro p hregular hvolume hscalar hpoissonCompact hinitial htrans hsplit hrigidity hharmonic hmeasured
  let := hX.hausdorff_regular
  exact regular_coordinates_of_published_inputs hn hX hregular hvolume
    (hX.poisson_hessian_action_input_of_scalar hn hscalar)
    (hX.poisson_gradient_product_input_of_scalar hn hscalar)
    hpoissonCompact (hX.poisson_hessian_input_of_scalar hn hscalar)
    hinitial htrans hsplit hrigidity hharmonic hmeasured

end RegularPointCoordinates

end

end OAI
