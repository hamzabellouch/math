import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Coordinates.RegularCenterRadialData

namespace OAI

/-! # A common regular neighborhood with uniform radial estimates -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The published inputs yield one actual heat and Poisson environment,
with the radial constants fixed before all requested smallness tolerances. -/
theorem exists_regular_radial_environment {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 2) X) [(hausdorff (m + 2) X).Regular]
    {p : X} {a κ : ℝ} (ha : 0 ≤ a) (hκ : 0 ≤ κ) (hK : -κ ≤ K)
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular (m + 2) p)
    (hvolume : EuclideanRescalingVolumeConvergence (hausdorff (m + 2) X) (m + 2) p
      (euclideanUnitVolume (m + 2)))
    (hmeasured : EuclideanMeasuredRescalingConvergence (hausdorff (m + 2) X) (m + 2) p)
    (hBG : BallVolumeComparison (hausdorff (m + 2) X) (comparisonModelVolume (m + 1) a))
    (hdensity : ∀ y, SmallScaleVolumeUpper (hausdorff (m + 2) X)
      (comparisonModelVolume (m + 1) a) y (euclideanUnitVolume (m + 2)))
    (hdistance : LocalSquaredDistanceInput hX) (hsobolev : LocalDirichletSobolevInput hX)
    (hpoisson : LocalPoissonGradientInput hX)
    (hhessian : LocalPoissonHessianInput hX) (hmean : LocalHarmonicL2MeanValueInput hX)
    (hinitial : LocalInitialSplittingInput hX) (htrans : LocalTransformationInput hX)
    (hsplit : LocalFlatSplittingInput hX) (hrigidity : UniformRegularFlatnessInput hX)
    (hbochner : LocalHarmonicBochnerInput hX) (hcutoff : LocalGoodCutoffInput hX)
    (hharmonic : LocalHarmonicMomentCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (heuclidean : EuclideanHarmonicHessianInput (m + 2))
    (hmetricmeasure : LocalMeasuredCoordinateInput hX)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff (m + 2) X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff (m + 2) X) ker)
    (hdiff : HasGaussianHeatDifferenceBounds (hausdorff (m + 2) X) ker) :
    letI : IsLocallyFiniteMeasure (hausdorff (m + 2) X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∃ B J C A Cχ Cg D Ca : ℝ,
      0 < B ∧ 0 < J ∧ 1 ≤ C ∧ 0 < A ∧ 1 ≤ Cχ ∧ 1 ≤ Cg ∧ 0 < D ∧ 1 ≤ Ca ∧
      ∀ enlargement zeta eta cap : ℝ, 0 ≤ enlargement → 0 < zeta →
      radialNormalizationRestrictionConstant (m + 2) * zeta ≤ 1 →
      ((m + 2 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio (m + 1) * zeta) ≤ 1 / 64 →
      0 < eta → 0 < cap →
      ∃ e : RegularProjectionEnvironment hX p hk a κ B J C A Cχ enlargement zeta eta,
        e.heat.radius ≤ cap ∧ ∀ q ∈ ball p (e.heat.radius / 32),
          Nonempty (RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca q) := by
  let : IsLocallyFiniteMeasure (hausdorff (m + 2) X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  obtain ⟨degree, hdegree, B, J, C, A, Cχ, hB, hJ, hC, hA, hCχ, hconstruct⟩ :=
    exists_regular_projection_environment_uniform_degree m hX ha hκ hK hcompact hregular
      hvolume hmeasured hBG hdensity hdistance hsobolev hpoisson hinitial htrans hsplit
      hrigidity hbochner hcutoff hharmonic hgradient heuclidean hmetricmeasure hk hg hdiff
  obtain ⟨Cg, D, Ca, hCg, hD, hCa, hrows⟩ := regular_center_radial_constants m hX hhessian
    hmean hgradient hB.le hJ.le hA.le (zero_le_one.trans hCχ) (by omega : 0 < degree)
  refine ⟨B, J, C, A, Cχ, Cg, D, Ca, hB, hJ, hC, hA, hCχ, hCg, hD, hCa, ?_⟩
  intro enlargement zeta eta cap henlargement hzeta hsmall1 hsmall heta hcap
  obtain ⟨e, hecap, hdeg⟩ := hconstruct enlargement zeta eta cap henlargement hzeta heta hcap
  exact ⟨e, hecap, hrows ha hκ hK hzeta.le hsmall1 hsmall hBG e hdeg⟩

end RegularPointCoordinates

end

end OAI
