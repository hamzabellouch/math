import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Coordinates.RegularCenterRadialData
import OAI.Geometry.RCD.Harmonic.ScaledProjectionEnvironment

namespace OAI

/-! # A common regular neighborhood with uniform radial estimates -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The published inputs yield one actual heat and Poisson environment,
with the radial constants fixed before all requested smallness tolerances. -/
theorem exists_scaled_radial_environment {K : ℝ} (m : ℕ)
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
    (hhessian : LocalPoissonHessianInput hX) (hproduct : LocalPoissonGradientProductInput hX)
    (hmean : LocalHarmonicL2MeanValueInput hX)
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
    ∃ c : RegularHeatConstants (m + 2), ∃ B J C A Cχ Cg D Ca : ℝ,
      0 < B ∧ 0 < J ∧ 1 ≤ C ∧ 0 < A ∧ 1 ≤ Cχ ∧ 1 ≤ Cg ∧ 0 < D ∧ 1 ≤ Ca ∧
      ∀ zeta eta cap : ℝ, 0 < zeta →
      radialNormalizationRestrictionConstant (m + 2) * zeta ≤ 1 →
      ((m + 2 : ℕ) : ℝ) ^ 2 * (normalizationVolumeRatio (m + 1) * zeta) ≤ 1 / 64 →
      0 < eta → 0 < cap →
      ∃ e : RegularProjectionEnvironment hX p hk a κ B J C A Cχ 1 zeta eta,
        e.heat.radius ≤ cap ∧ c.Matches e.heat ∧ ∀ q ∈ ball p (e.heat.radius / 32),
          Nonempty (RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca q) := by
  let : IsLocallyFiniteMeasure (hausdorff (m + 2) X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  obtain ⟨c, B, J, C, A, Cχ, hB, hJ, hC, hA, hCχ, hconstruct⟩ :=
    exists_scaled_projection_environment m hX ha hκ hK hcompact hregular
      hvolume hmeasured hBG hdensity hdistance hsobolev hpoisson hinitial htrans hsplit
      hrigidity hbochner hcutoff hhessian hproduct hharmonic hgradient heuclidean hmetricmeasure hk hg hdiff
  obtain ⟨Cg, D, Ca, hCg, hD, hCa, hrows⟩ := regular_center_radial_constants m hX hhessian
    hmean hgradient hB.le hJ.le hA.le (zero_le_one.trans hCχ) (show 0 < c.degree from lt_of_lt_of_le (by norm_num) c.degree_ge_three)
  refine ⟨c, B, J, C, A, Cχ, Cg, D, Ca, hB, hJ, hC, hA, hCχ, hCg, hD, hCa, ?_⟩
  intro zeta eta cap hzeta hsmall1 hsmall heta hcap
  obtain ⟨e, hecap, hmatch⟩ := hconstruct zeta eta cap hzeta heta hcap
  exact ⟨e, hecap, hmatch, hrows ha hκ hK hzeta.le hsmall1 hsmall hBG e hmatch.1⟩

end RegularPointCoordinates

end

end OAI
