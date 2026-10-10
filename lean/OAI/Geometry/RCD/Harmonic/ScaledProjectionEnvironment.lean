import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Coordinates.RegularProjectionEnvironment
import OAI.Geometry.RCD.Coordinates.ScaledRegularData

namespace OAI

/-! # Actual Poisson environments retaining fixed heat constants -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The radius cap synchronizes the already proved heat construction with
the source neighborhood. All five construction constants are chosen before
the source and coordinate tolerances. -/
theorem exists_scaled_projection_environment {K : ℝ} (m : ℕ)
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
    (hinitial : LocalInitialSplittingInput hX) (htrans : LocalTransformationInput hX)
    (hsplit : LocalFlatSplittingInput hX) (hrigidity : UniformRegularFlatnessInput hX)
    (hbochner : LocalHarmonicBochnerInput hX) (hcutoff : LocalGoodCutoffInput hX)
    (hhessian : LocalPoissonHessianInput hX) (hproduct : LocalPoissonGradientProductInput hX)
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
    ∃ c : RegularHeatConstants (m + 2), ∃ B J C A Cχ : ℝ, 0 < B ∧ 0 < J ∧ 1 ≤ C ∧ 0 < A ∧ 1 ≤ Cχ ∧
      ∀ zeta eta cap : ℝ, 0 < zeta → 0 < eta → 0 < cap →
      ∃ d : RegularProjectionEnvironment hX p hk a κ B J C A Cχ 1 zeta eta,
        d.heat.radius ≤ cap ∧ c.Matches d.heat := by
  let : IsLocallyFiniteMeasure (hausdorff (m + 2) X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  obtain ⟨c, hheatConstruct⟩ := exists_scaled_regular_bilinear_data m hX
    ha hcompact hregular hvolume hmeasured hBG hdensity hinitial htrans hsplit hrigidity
    hbochner hcutoff hhessian hproduct hharmonic hgradient heuclidean hmetricmeasure hk hg hdiff 1 (by norm_num)
  have hn : 2 ≤ m + 2 := by omega
  obtain ⟨B, J, C, hB, hJ, hC, hsources⟩ := regular_poisson_defect_uniform m hX
    ha hκ hK hcompact hregular hvolume hBG hdensity hdistance hsobolev hcutoff
  obtain ⟨A, hA, hgrad⟩ := poisson_family_gradient hX hn hpoisson (B := B) hκ
  obtain ⟨Cχ, hCχ, hcuts⟩ := hcutoff hn
  refine ⟨c, B, J, C, A, Cχ, hB, hJ, hC, hA, hCχ, ?_⟩
  intro zeta eta cap hzeta heta hcap
  let cap' := min cap (1 / (4 * (|K| + κ + a + 1)))
  have hcap' : 0 < cap' := lt_min hcap (by positivity)
  obtain ⟨D, hD, hDcap, hsource⟩ := hsources cap' eta hcap' heta
  obtain ⟨heat, hheat, hmatch⟩ := hheatConstruct (radiusCap := D / 2)
    (by positivity) hzeta
  let R := heat.radius
  have hR : 0 < R := heat.radius_pos
  have hR1 : R ≤ 1 := heat.radius_le_one
  have hRcap : R ≤ cap' := hheat.trans ((by linarith : D / 2 ≤ D).trans hDcap)
  have hRsmall : R ≤ 1 / (4 * (|K| + κ + a + 1)) := hRcap.trans (min_le_right _ _)
  have hbound := (le_div_iff₀ (by positivity : 0 < 4 * (|K| + κ + a + 1))).mp hRsmall
  have hscale : a * (3 * R) ≤ 1 := by
    nlinarith [mul_nonneg (abs_nonneg K) hR.le, mul_nonneg hκ hR.le, mul_nonneg ha hR.le]
  have hcurv : 4 * (|K| + κ) * R ^ 2 ≤ 1 := by
    have hsquare : R ^ 2 ≤ R := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hsquare (by positivity : 0 ≤ 4 * (|K| + κ))
    nlinarith [mul_nonneg ha hR.le]
  have hcurvSmall (r : ℝ) (hr : 0 ≤ r) (hrR : r ≤ 2 * R) : -1 ≤ K * r ^ 2 := by
    have hsquare : r ^ 2 ≤ (2 * R) ^ 2 := by nlinarith
    have habs := mul_le_mul_of_nonneg_left hsquare (abs_nonneg K)
    have hlo := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg r)
    have hkappa := mul_nonneg hκ (sq_nonneg R)
    nlinarith
  let one := Classical.choice (hcuts p (2 * R) (by positivity)
    (hcurvSmall _ (by positivity) le_rfl))
  have hqD (q : X) (hq : q ∈ ball p (R / 32)) : dist p q ≤ D := by
    have hh := mem_ball.mp hq
    rw [dist_comm] at hh
    linarith
  have hvol (q : X) (hq : q ∈ ball p (R / 32)) (t : ℝ) (ht : 0 < t) (htR : t ≤ 2 * R) :
      |(hausdorff (m + 2) X).real (ball q t) /
        (euclideanUnitVolume (m + 2) * t ^ (m + 2)) - 1| ≤ 1 / 4 := by
    obtain ⟨_, _, _, _, hv⟩ := hsource q (hqD q hq) (2 * R) (by positivity) (by linarith)
    exact hv t ht htR
  refine ⟨{
    heat := heat
    modelScale := hscale
    curvature := hcurv
    one := one
    oneRepresentative := ?_
    volume := hvol
    poisson := ?_ }, hRcap.trans (min_le_left _ _), hmatch⟩
  · intro q hq i
    filter_upwards [ae_restrict_of_ae one.representative, ae_restrict_mem measurableSet_ball]
      with x hx hball
    rw [hx]
    apply one.one
    have houter := distanceSourceRadius_outer_le hR.le i
    have hxq := mem_ball.mp hball
    have hqp := mem_ball.mp hq
    have hxp := dist_triangle x q p
    change dist x p < 2 * R
    linarith
  · intro q hq
    obtain ⟨S, hT, hsum, hbudget, _⟩ := hsource q (hqD q hq) R hR (by linarith)
    let T := Classical.choice hT
    have hs (i : ℕ) : 0 < distanceSourceRadius R i := distanceSourceRadius_pos hR i
    have hsR (i : ℕ) : distanceSourceRadius R i ≤ R := by
      have hh := distanceSourceRadius_outer_le hR.le i
      linarith
    refine ⟨S, T, hsum, hbudget, ?_, ?_⟩
    · intro i z hz
      have hsi := hs i
      exact hgrad q z R J C S T i ((hsR i).trans hR1) hz
        (hcurvSmall _ (by positivity) (by linarith [hsR i]))
    · intro i
      have hsi := hs i
      exact hcuts q _ (by positivity) (hcurvSmall _ (by positivity) (by linarith [hsR i]))


end RegularPointCoordinates

end

end OAI
