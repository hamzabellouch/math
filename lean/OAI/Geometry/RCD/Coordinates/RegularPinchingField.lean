import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Coordinates.RegularMeanPinchingNeighborhood

namespace OAI

/-! # One actual matrix and energy family for all finite patches -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- These are constructed from the original full Bochner measure and the
actual Poisson sources. The common positive floor permits a fixed energy
minimizer in each finite patch. -/
structure RegularPinchingField {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    [(hausdorff n X).Regular] {base : X} {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    {enlargement zeta : ℝ} (d : RegularBilinearData hX base hk enlargement zeta)
    (C budget : ℝ) where
  energy : {q : X // q ∈ ball base (d.radius / 32)} → ℕ → ℝ
  floor : ℕ → ℝ
  floor_pos : ∀ i, 0 < floor i
  energy_floor : ∀ q i, floor i ≤ energy q i
  summable : ∀ q, Summable (energy q)
  total : ∀ q, (∑' i, energy q i) ≤ budget
  directional : ∀ x z i,
    dist x.val z.val ≤ distanceSourceRadius d.radius i / 512 →
    ⟪d.values x.val - d.values z.val,
      d.pinchingMassMatrix z.val z.property i (d.values x.val - d.values z.val)⟫_ℝ ≤
      C * (distanceSourceRadius d.radius i) ^ 2 * (energy x i + energy z i)

theorem exists_regular_pinching_field {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 2) X) [(hausdorff (m + 2) X).Regular]
    {p : X} {a : ℝ} (ha : 0 ≤ a)
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular (m + 2) p)
    (hvolume : EuclideanRescalingVolumeConvergence (hausdorff (m + 2) X) (m + 2) p
      (euclideanUnitVolume (m + 2)))
    (hmeasured : EuclideanMeasuredRescalingConvergence (hausdorff (m + 2) X) (m + 2) p)
    (hBG : BallVolumeComparison (hausdorff (m + 2) X) (comparisonModelVolume (m + 1) a))
    (hdensity : ∀ y, SmallScaleVolumeUpper (hausdorff (m + 2) X)
      (comparisonModelVolume (m + 1) a) y (euclideanUnitVolume (m + 2)))
    (hdistance : LocalSquaredDistanceInput hX) (hsobolev : LocalDirichletSobolevInput hX)
    (hpoisson : LocalPoissonGradientInput hX)
    (haction : LocalPoissonHessianActionInput hX)
    (hproduct : LocalPoissonGradientProductInput hX)
    (hpoincare : LocalMeanPoincareInput hX)
    (hpoissonCompact : LocalPoissonHarmonicCompactnessInput hX)
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
    ∃ B J C A Cχ Cpin : ℝ,
      0 < B ∧ 0 < J ∧ 1 ≤ C ∧ 0 < A ∧ 1 ≤ Cχ ∧ 0 < Cpin ∧
      ∀ budget : ℝ, 0 < budget → ∃ zeta eta : ℝ, 0 < zeta ∧ 0 < eta ∧
      ∃ e : RegularProjectionEnvironment hX p hk a |K| B J C A Cχ 1 zeta eta,
        zeta ≤ budget ∧ Nonempty (RegularPinchingField e.heat Cpin budget) := by
  classical
  let : IsLocallyFiniteMeasure (hausdorff (m + 2) X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  obtain ⟨B, J, C, A, Cχ, Cg, D, Ca, Cpin, hB, hJ, hC, hA, hCχ, hCg, hD, hCa, hCpin, hbuild⟩ :=
    exists_regular_mean_pinching_neighborhood m hX ha hcompact hregular hvolume hmeasured
      hBG hdensity hdistance hsobolev hpoisson haction hproduct hpoincare hpoissonCompact
      hhessian hmean hinitial htrans hsplit hrigidity hbochner hcutoff hharmonic hgradient
      heuclidean hmetricmeasure hk hg hdiff
  refine ⟨B, J, C, A, Cχ, Cpin, hB, hJ, hC, hA, hCχ, hCpin, ?_⟩
  intro budget hbudget
  obtain ⟨zeta, eta, hzeta, heta, e, data, hpairs⟩ := hbuild budget hbudget
  let μ := hausdorff (m + 2) X
  let Q := radialFitQualitativeConstant (m + 2) Cχ * zeta
  have hQ : 0 < Q := by
    have hc : 0 < radialNormalizationRestrictionConstant (m + 2) :=
      zero_lt_one.trans_le (radialNormalizationRestrictionConstant_ge_one (m + 2))
    have hqual : 0 < radialFitQualitativeConstant (m + 2) Cχ := by
      dsimp only [radialFitQualitativeConstant]
      change 0 < ((m + 2 : ℕ) : ℝ) * (1000 * (((m + 2 : ℕ) : ℝ) + 1) ^ 2 * (Cχ + 1)) *
        radialNormalizationRestrictionConstant (m + 2) * _
      positivity
    exact mul_pos hqual hzeta
  let P := fun q : {q : X // q ∈ ball p (e.heat.radius / 32)} =>
    normalizedPoissonDefect μ hX.quadratic (data q.val q.property).source
  let E := fun q => pinchingEnvelope (7 / 8) (3 / 4) Q (P q)
  have hP (q) (i) : 0 ≤ P q i :=
    normalizedPoissonDefect_nonneg μ hX.quadratic (data q.val q.property).source (abs_nonneg K) i
  have hspec (q) := pinchingEnvelope_spec (by norm_num : (0 : ℝ) < 7 / 8)
    (by norm_num : (7 / 8 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1) hQ (hP q) (data q.val q.property).summable
  have hE (q) (i) : 0 ≤ E q i := ((hspec q).2.2 i).2.2.le
  have hsig (x z) (i) :
      twoCenterProjectionSource Q (P x) (P z) i ^ 2 = E x i + E z i :=
    Real.sq_sqrt (add_nonneg (hE x i) (hE z i))
  have htotal (q) : (∑' i, E q i) ≤ budget := by
    obtain ⟨hsum, hbound, _⟩ := hpairs q.val q.property q.val q.property
    have hdom (i) : E q i ≤ twoCenterProjectionSource Q (P q) (P q) i ^ 2 := by
      rw [hsig]
      linarith [hE q i]
    exact (((hspec q).1).tsum_le_tsum hdom hsum).trans hbound
  have hqual : 1 ≤ radialFitQualitativeConstant (m + 2) Cχ := by
    have hn : (1 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ m + 2 by omega)
    have hs : (1 : ℝ) ≤ (((m + 2 : ℕ) : ℝ) + 1) ^ 2 := by nlinarith
    have hb : (1 : ℝ) ≤ 1000 * (((m + 2 : ℕ) : ℝ) + 1) ^ 2 * (Cχ + 1) := by
      have hh := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 1000)
      have hprod := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ Cχ + 1 by linarith)
        (show 0 ≤ 1000 * (((m + 2 : ℕ) : ℝ) + 1) ^ 2 by positivity)
      nlinarith
    have hfirst : (1 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) *
        (1000 * (((m + 2 : ℕ) : ℝ) + 1) ^ 2 * (Cχ + 1)) := by nlinarith
    have hsecond := radialNormalizationRestrictionConstant_ge_one (m + 2)
    have hthird : (1 : ℝ) ≤ (5 / 3 : ℝ) * (4 : ℝ) ^ (m + 2) := by
      have hp : (1 : ℝ) ≤ 4 ^ (m + 2) := one_le_pow₀ (by norm_num)
      linarith
    dsimp only [radialFitQualitativeConstant]
    have hp := mul_le_mul hfirst hsecond (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) *
        (1000 * (((m + 2 : ℕ) : ℝ) + 1) ^ 2 * (Cχ + 1)))
    have hp' := mul_le_mul hp hthird (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
    simpa only [one_mul] using hp'
  have hzetaBudget : zeta ≤ budget := by
    let q : {q : X // q ∈ ball p (e.heat.radius / 32)} :=
      ⟨p, mem_ball_self (div_pos e.heat.radius_pos (by norm_num))⟩
    have hfloor : Q ≤ E q 0 := by simpa only [pow_zero, mul_one] using ((hspec q).2.2 0).2.1
    have he0 := (hspec q).1.le_tsum 0 (fun j _ => hE q j)
    have hQz : zeta ≤ Q := by
      dsimp only [Q]
      nlinarith [mul_le_mul_of_nonneg_right hqual hzeta.le]
    exact hQz.trans (hfloor.trans (he0.trans (htotal q)))
  refine ⟨zeta, eta, hzeta, heta, e, hzetaBudget, ⟨{
    energy := E
    floor := fun i => Q * (7 / 8 : ℝ) ^ i
    floor_pos := fun i => mul_pos hQ (pow_pos (by norm_num) i)
    energy_floor := fun q i => ((hspec q).2.2 i).2.1
    summable := fun q => (hspec q).1
    total := htotal
    directional := ?_ }⟩⟩
  · intro x z i hroom
    have hh := (hpairs x.val x.property z.val z.property).2.2 i hroom
    rw [hsig] at hh
    exact hh.2

end RegularPointCoordinates

end

end OAI
