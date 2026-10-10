import OAI.Geometry.RCD.Coordinates.HausdorffMeasureRegularity
import OAI.Geometry.RCD.Sobolev.DistanceLaplacian
import OAI.Geometry.RCD.Coordinates.CanonicalCoordinateHeatInput
import OAI.Geometry.RCD.Metric.ModelVolumeComparison
import OAI.Geometry.RCD.Coordinates.ConditionalMain
import OAI.Geometry.RCD.Sobolev.HarmonicBochnerFromHessian
import OAI.Geometry.RCD.Coordinates.Proper
import OAI.Geometry.RCD.Sobolev.HarmonicGradientFromPoisson
import OAI.Geometry.RCD.Sobolev.GoodCutoffFromResolvent
import OAI.Geometry.RCD.Metric.PointedCompactness
import OAI.Geometry.RCD.Coordinates.GevreyCutoffConstruction
import OAI.Geometry.RCD.Transport.TransportPoincare
import OAI.Geometry.RCD.Coordinates.MeasuredRescalingFromCoordinates
import OAI.Geometry.RCD.Metric.VolumeDensity
import OAI.Geometry.RCD.Sobolev.DirichletSobolevConstruction
import OAI.Geometry.RCD.Harmonic.HarmonicMeanConstruction
import OAI.Geometry.RCD.Heat.KernelGaussianDifference
import OAI.Geometry.RCD.Sobolev.PoissonGradientConstruction
import OAI.Geometry.RCD.Sobolev.EuclideanHarmonicHessianConstruction
import OAI.Geometry.RCD.Heat.CanonicalKernelConstruction
import OAI.Geometry.RCD.Heat.CanonicalGaussianDifference

namespace OAI

/-! # Local analytic estimates for regular-point coordinates

Hausdorff measure is regular by local finiteness on proper separable spaces.
Finite-span Poisson Hessian estimates imply the harmonic Bochner calculus.
Heat resolvents construct cutoffs, and bounded-compression transport yields
local Poincare and zero-boundary Sobolev inequalities. These estimates give
harmonic mean-value bounds and Poisson gradient estimates at every radius.
The heat semigroup has a continuous kernel with Gaussian bounds. Compact-test
integration by parts and radial mean kernels give Euclidean harmonic Hessian
estimates. Sharp annular contraction yields model Bishop--Gromov comparison,
and compressed radial transport yields the squared-distance Laplacian estimate.
-/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The chart conclusion follows from local analytic estimates and
pointed rescaling compactness. Finite nets and completed distance matrices
give the latter; volume comparison and completeness give properness. -/
theorem regular_coordinates_of_published_inputs {K : ℝ} {n : ℕ}
    (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) :
    let _ := hX.properSpace hn
    ∀ {p : X}
    (_hregular : IsRegular n p)
    (_hvolume : EuclideanRescalingVolumeConvergence (hausdorff n X) n p
      (euclideanUnitVolume n))
    (_haction : LocalPoissonHessianActionInput hX)
    (_hproduct : LocalPoissonGradientProductInput hX)
    (_hpoissonCompact : LocalPoissonHarmonicCompactnessInput hX)
    (_hhessian : LocalPoissonHessianInput hX)
    (_hinitial : LocalInitialSplittingInput hX) (_htrans : LocalTransformationInput hX)
    (_hsplit : LocalFlatSplittingInput hX) (_hrigidity : LocalVolumeRigidityInput hX)
    (_hharmonic : LocalHarmonicMomentCompactnessInput hX)
    (_hmetricmeasure : LocalMeasuredCoordinateInput hX),
    HasOpenBilipschitzChart n p := by
  let := hX.properSpace hn
  dsimp only
  intro p hregular hvolume
    haction hproduct hpoissonCompact hhessian hinitial htrans
    hsplit hrigidity hharmonic hmetricmeasure
  let := hX.hausdorff_regular
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  obtain ⟨a, ha, hBG⟩ := hX.exists_model_ballVolumeComparison hn
  have hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  have hg := hX.canonicalHeatKernel_coordinateBounds hn p
  have hpoisson := hX.poissonGradientInput hk hg hhessian
  have heuclidean := euclideanHarmonicHessianInput (n := n) (by omega)
  exact every_regular_point_has_bilipschitz_coordinates_of_flat_coordinate_heat_bounds hn hX ha (hX.pointedRescalingPrecompactness hn p) hregular
    hvolume (hmetricmeasure.euclideanMeasuredRescalingConvergence hn p) hBG
    (hX.smallScaleVolumeUpper hn ha) hX.localSquaredDistanceInput hX.localDirichletSobolevInput hpoisson haction hproduct
    (hX.localMeanPoincareInput hn)
    hpoissonCompact hhessian hX.harmonicMeanValueInput hinitial htrans hsplit hrigidity
    hhessian.harmonicBochnerInput hX.goodCutoffInput hharmonic
    (harmonicGradientInput_of_poisson_and_mean hX hpoisson hX.harmonicMeanValueInput) heuclidean hmetricmeasure
    hk hg (hX.canonicalHeatKernel_gaussian_difference hn p) (euclideanGevreyCutoffInput n)

end RegularPointCoordinates

end

end OAI
