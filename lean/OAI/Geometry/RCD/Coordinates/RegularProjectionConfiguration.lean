import OAI.Geometry.RCD.Coordinates.RegularProjectionRows
import OAI.Geometry.RCD.Harmonic.LocalProjectionMeasure
import OAI.Geometry.RCD.Coordinates.NormalizedProjectionConfiguration

namespace OAI

/-! # Sharp-projection configurations constructed from the regular neighborhood -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The actual radial rows construct the full projection data. The affine
constant is fixed before the measured error and every geometric choice. -/
theorem regular_projection_configuration_constants {K : ℝ} (m : ℕ)
    (hX : NoncollapsedRCD K (m + 2) X) [(hausdorff (m + 2) X).Regular]
    (hgradient : LocalHarmonicL2GradientInput hX) (hmean : LocalHarmonicL2MeanValueInput hX)
    (hmeasured : LocalMeasuredCoordinateInput hX)
    {κ B J C A Cχ epsilon D : ℝ}
    (hκ : 0 ≤ κ) (hK : -κ ≤ K) (hB : 0 ≤ B) (hCχ : 0 ≤ Cχ)
    (hepsilon : 0 ≤ epsilon)
    (hsmall : ((m + 2 : ℕ) : ℝ) ^ 2 *
      (((5 / 3 : ℝ) * (16384 : ℝ) ^ (m + 2)) * epsilon) ≤ 1 / 2) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ error : ℝ, 0 < error → ∃ delta : ℝ, 0 < delta ∧
    ∀ {base first center : X} {a enlargement zeta eta Cg Ca : ℝ}
      {ker : ℝ → X → X → ℝ}
      {hk : IsContinuousHeatKernel (hausdorff (m + 2) X) hX.quadratic ker},
      0 ≤ a → 0 ≤ zeta → zeta ≤ epsilon → zeta ≤ delta → 0 ≤ eta →
      BallVolumeComparison (hausdorff (m + 2) X) (comparisonModelVolume (m + 1) a) →
      ∀ e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta,
      first ∈ ball base (e.heat.radius / 32) → center ∈ ball base (e.heat.radius / 32) →
      ∀ (d1 : RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca first)
        (d2 : RegularCenterRadialData hX e.heat κ B J C A Cχ eta Cg D Ca center) (i : ℕ),
      let s := distanceSourceRadius e.heat.radius i
      let uc := centeredColumn (hausdorff (m + 2) X) hX.quadratic
        (transformedColumn (hausdorff (m + 2) X) hX.quadratic e.heat.coordinates (d2.frame i))
        ((d2.frame i : Euclidean (m + 2) →L[ℝ] Euclidean (m + 2)).adjoint (e.heat.values center))
        e.one.sobolev
      dist center first ≤ s / 4 → -delta / 32 ≤ K * s ^ 2 →
      ∀ source : ℝ, 0 < source →
      normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic d1.source i +
        normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic d2.source i ≤ source ^ 2 →
      pinchingEnvelope (7 / 8) (3 / 4) (radialFitQualitativeConstant (m + 2) Cχ * zeta)
        (normalizedPoissonDefect (hausdorff (m + 2) X) hX.quadratic d2.source) i ≤ source ^ 2 →
      ∃ d : ActualProjectionConfiguration hX κ B J C A Cχ epsilon H
        (((m + 2 : ℕ) : ℝ) * Real.sqrt (projectionRowConstant (m + 2) B D)) 1 1,
        d.radius = s ∧ d.source = source ∧ d.totalSource = eta ∧
        d.approximationError = error ∧ d.coordinates = uc ∧ d.center = center ∧
        d.projectionNorm =
          ‖normalizeLocalL2 (hausdorff (m + 2) X) (ball center ((1 / 2048) * s))
            (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
            (affineResidual (hausdorff (m + 2) X) hX.quadratic
              (radiusScaledColumns (hausdorff (m + 2) X) hX.quadratic s uc)
              (ball center ((1 / 2048) * s)) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
              (SobolevSpace.restrictLp (hausdorff (m + 2) X) hX.quadratic
                (ball center ((1 / 2048) * s))
                ((s ^ 2)⁻¹ • (d2.replacement.replacement i - d1.replacement.replacement i))))‖ := by
  classical
  have hn : 2 ≤ m + 2 := by omega
  have hDrow := projectionRowConstant_nonneg (m + 2) (D := D) hB
  obtain ⟨H, hH, hconstruct⟩ := normalized_projection_configuration hX hgradient hmean hn
    hκ hepsilon hDrow hsmall
  refine ⟨H, hH, ?_⟩
  intro error herror
  obtain ⟨deltaM, hdeltaM, hmeasure⟩ := projection_measured_local_coordinates hX hn hmeasured herror
  let delta := min deltaM 1
  have hdelta : 0 < delta := lt_min hdeltaM zero_lt_one
  refine ⟨delta, hdelta, ?_⟩
  intro base first center a enlargement zeta eta Cg Ca ker hk ha hzeta hzetaeps hzetadelta heta hBG
    e hfirst hcenter d1 d2 i s uc hroom hcurvMeasure source hsource hpair henv
  let μ := hausdorff (m + 2) X
  let hQ := hX.quadratic
  have hs : 0 < s := distanceSourceRadius_pos e.heat.radius_pos i
  have hs2R : 2 * s ≤ e.heat.radius := distanceSourceRadius_outer_le e.heat.radius_pos.le i
  have hR1 := e.heat.radius_le_one
  have hsR : s ≤ e.heat.radius := by linarith
  obtain ⟨huc, hnormal, hmetric, g, coeff, hrows⟩ :=
    regular_center_projection_rows hX e hcenter d2 hκ hB hCχ hzeta i
  let V := fun x => (d2.frame i : Euclidean (m + 2) →L[ℝ] Euclidean (m + 2)).adjoint (e.heat.values x) -
    (d2.frame i : Euclidean (m + 2) →L[ℝ] Euclidean (m + 2)).adjoint (e.heat.values center)
  have hVzero : V center = 0 := sub_self _
  have huc' : FirstOrderSplittingOn μ hQ center (2 * s) epsilon uc V :=
    huc.mono_error μ hQ hzeta hzetaeps
  have hzetaM : zeta ≤ deltaM := hzetadelta.trans (min_le_left _ _)
  have hzeta1 : zeta ≤ 1 := hzetadelta.trans (min_le_right _ _)
  have hcurvM : -deltaM / 32 ≤ K * s ^ 2 := by
    have hh : delta ≤ deltaM := min_le_left _ _
    linarith
  obtain ⟨W, _hW, hEq, hWfirst, hWzero, _hWmetricM, hWmeasured⟩ :=
    hmeasure hs hcurvM uc V huc' hVzero (hmetric.mono_error hzetaM)
  have hWmetric : IsPointedApproximation center 0 (s / 64) 4 zeta
      (fun x => (s / 64)⁻¹ • W x) := by
    apply hmetric.congr_on_ball (by positivity)
    intro x hx
    have hxs : x ∈ ball center (2 * s) := by
      have hh := mem_closedBall.mp hx
      exact mem_ball.mpr (by linarith)
    change (s / 64)⁻¹ • V x = (s / 64)⁻¹ • W x
    rw [hEq hxs]
  have hcurv : -1 ≤ K * s ^ 2 := by
    have hh := e.curvature
    have hsq : s ^ 2 ≤ e.heat.radius ^ 2 := by nlinarith
    have habs := mul_le_mul_of_nonneg_left hsq (abs_nonneg K)
    have hlo := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg s)
    have hkR := mul_nonneg hκ (sq_nonneg e.heat.radius)
    nlinarith
  have hsmallcurv : -κ ≤ K * (s / 512) ^ 2 := by
    have hsq : (s / 512) ^ 2 ≤ 1 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hK (sq_nonneg (s / 512))
    have hk := mul_nonneg hκ (sub_nonneg.mpr hsq)
    nlinarith
  have hlap : ((m + 2 : ℕ) : ℝ) + κ * (4 * s) ^ 2 ≤ ((m + 2 : ℕ) : ℝ) + 1 := by
    have hsq : (4 * s) ^ 2 ≤ 4 * e.heat.radius ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hsq hκ
    have he := e.curvature
    have haR := mul_nonneg (abs_nonneg K) (sq_nonneg e.heat.radius)
    nlinarith
  have hsphere : μ (sphere center (s / 2048)) = 0 :=
    sphere_measure_zero_of_comparison hBG (continuous_comparisonModelVolume (m + 1) a)
      center (by positivity) (comparisonModelVolume_pos (m + 1) ha (by positivity))
  apply hconstruct e.heat.radius first center d1.source d2.source d1.replacement d2.replacement i
    hR1 hroom hcurv hsmallcurv hlap
    (fun t ht htR => e.volume center hcenter t ht (by linarith)) hsphere
    uc W hWfirst hnormal hWzero zeta hzeta1 hWmetric error herror hWmeasured
    e.one.sobolev (e.oneRepresentative center hcenter i) (d2.cutoff i)
    (d1.gradient i center hroom) (d2.gradient i center (by simp only [dist_self]; positivity))
    source hsource hpair g coeff (fun j => (hrows j).1) _ eta heta d2.summable d2.budget.le
  intro j
  exact (hrows j).2.trans (mul_le_mul_of_nonneg_left henv (by positivity))

end RegularPointCoordinates

end

end OAI
