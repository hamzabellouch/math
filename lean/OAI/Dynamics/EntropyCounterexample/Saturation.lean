import Mathlib

namespace OAI

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff

namespace Problem340

def saturationDerivative : ContDiffBump (0 : ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def saturationPrimitive (r : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..r, saturationDerivative t

theorem saturationPrimitive_hasDerivAt (r : ℝ) :
    HasDerivAt saturationPrimitive (saturationDerivative r) r := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact saturationDerivative.continuous.intervalIntegrable _ _
  · exact saturationDerivative.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
  · exact saturationDerivative.continuous.continuousAt

theorem saturationPrimitive_contDiff : ContDiff ℝ ∞ saturationPrimitive := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun r => (saturationPrimitive_hasDerivAt r).differentiableAt, ?_⟩
  have h : deriv saturationPrimitive = saturationDerivative :=
    funext fun r => (saturationPrimitive_hasDerivAt r).deriv
  rw [h]
  exact saturationDerivative.contDiff

theorem saturationPrimitive_nonneg {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ saturationPrimitive r := by
  exact intervalIntegral.integral_nonneg_of_forall hr saturationDerivative.nonneg'

theorem saturationPrimitive_eq_self {r : ℝ} (hr : |r| ≤ 1) :
    saturationPrimitive r = r := by
  have h : saturationPrimitive r = ∫ t in (0 : ℝ)..r, (1 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply saturationDerivative.one_of_mem_closedBall
    change dist t 0 ≤ (1 : ℝ)
    rw [Real.dist_eq, sub_zero]
    rcases mem_uIcc.mp ht with ht | ht
    · exact abs_le.mpr ⟨by linarith [abs_nonneg r], le_trans ht.2 (le_abs_self r |>.trans hr)⟩
    · exact abs_le.mpr ⟨le_trans (neg_abs_le r |>.trans' (neg_le_neg hr)) ht.1, by linarith⟩
  simpa [saturationPrimitive] using h

theorem saturationPrimitive_monotone : Monotone saturationPrimitive := by
  apply monotone_of_hasDerivAt_nonneg saturationPrimitive_hasDerivAt
  intro r
  exact saturationDerivative.nonneg

theorem saturationPrimitive_eq_at_two {r : ℝ} (hr : 2 ≤ r) :
    saturationPrimitive r = saturationPrimitive 2 := by
  have htail : (∫ t in (2 : ℝ)..r, saturationDerivative t) = 0 := by
    calc
      _ = ∫ t in (2 : ℝ)..r, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        apply saturationDerivative.zero_of_le_dist
        change (2 : ℝ) ≤ dist t 0
        rw [Real.dist_eq, sub_zero, abs_of_nonneg]
        · exact ((uIcc_of_le hr) ▸ ht).1
        · have := ((uIcc_of_le hr) ▸ ht).1
          linarith
      _ = 0 := by simp
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (saturationDerivative.continuous.intervalIntegrable (μ := volume) 0 2)
    (saturationDerivative.continuous.intervalIntegrable (μ := volume) 2 r)
  simpa [saturationPrimitive, htail] using hsum.symm

theorem saturationPrimitive_le_two {r : ℝ} (_hr : 0 ≤ r) :
    saturationPrimitive r ≤ 2 := by
  have htwo : saturationPrimitive 2 ≤ 2 := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..2, (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (saturationDerivative.continuous.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)
        intro t ht
        exact saturationDerivative.le_one
      _ = 2 := by norm_num
  rcases le_total r 2 with h | h
  · exact (saturationPrimitive_monotone h).trans htwo
  · rw [saturationPrimitive_eq_at_two h]
    exact htwo

def saturationCutoff (R : ℝ) (hR : 1 ≤ R) : ContDiffBump (0 : ℝ) :=
  ⟨R, R + 1, by linarith, by linarith⟩

def saturationProfile (R : ℝ) (hR : 1 ≤ R) (r : ℝ) : ℝ :=
  saturationCutoff R hR r * saturationPrimitive r

theorem saturationProfile_contDiff (R : ℝ) (hR : 1 ≤ R) :
    ContDiff ℝ ∞ (saturationProfile R hR) :=
  (saturationCutoff R hR).contDiff.mul saturationPrimitive_contDiff

theorem saturationProfile_nonneg (R : ℝ) (hR : 1 ≤ R) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ saturationProfile R hR r :=
  mul_nonneg (saturationCutoff R hR).nonneg (saturationPrimitive_nonneg hr)

theorem saturationProfile_le_two (R : ℝ) (hR : 1 ≤ R) {r : ℝ} (hr : 0 ≤ r) :
    saturationProfile R hR r ≤ 2 := by
  calc
    _ ≤ 1 * saturationPrimitive r := mul_le_mul_of_nonneg_right
      (saturationCutoff R hR).le_one (saturationPrimitive_nonneg hr)
    _ ≤ 2 := by simpa using saturationPrimitive_le_two hr

theorem saturationProfile_eq_primitive (R : ℝ) (hR : 1 ≤ R) {r : ℝ}
    (hr : |r| ≤ R) : saturationProfile R hR r = saturationPrimitive r := by
  unfold saturationProfile
  rw [(saturationCutoff R hR).one_of_mem_closedBall (by simpa [Real.dist_eq, saturationCutoff] using hr)]
  simp

theorem saturationProfile_eq_self (R : ℝ) (hR : 1 ≤ R) {r : ℝ}
    (hr : |r| ≤ 1) : saturationProfile R hR r = r := by
  rw [saturationProfile_eq_primitive R hR (hr.trans hR), saturationPrimitive_eq_self hr]

theorem saturationProfile_eq_zero (R : ℝ) (hR : 1 ≤ R) {r : ℝ}
    (hr : R + 1 ≤ r) : saturationProfile R hR r = 0 := by
  unfold saturationProfile
  rw [(saturationCutoff R hR).zero_of_le_dist]
  · simp
  · simpa [Real.dist_eq, saturationCutoff, abs_of_nonneg (by linarith : 0 ≤ r)] using hr

theorem saturationProfile_monotoneOn (R : ℝ) (hR : 1 ≤ R) :
    MonotoneOn (saturationProfile R hR) (Icc 0 R) := by
  intro a ha b hb hab
  rw [saturationProfile_eq_primitive R hR (by simpa [abs_of_nonneg ha.1] using ha.2),
    saturationProfile_eq_primitive R hR (by simpa [abs_of_nonneg hb.1] using hb.2)]
  exact saturationPrimitive_monotone hab

def saturation (R : ℝ) (hR : 1 ≤ R) (z : ℂ) : ℂ :=
  (saturationProfile R hR ‖z‖ / ‖z‖) • z

@[simp] theorem saturation_zero (R : ℝ) (hR : 1 ≤ R) :
    saturation R hR 0 = 0 := by
  simp [saturation]

theorem saturation_eq_self (R : ℝ) (hR : 1 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    saturation R hR z = z := by
  by_cases hzero : z = 0
  · subst z
    exact saturation_zero R hR
  · unfold saturation
    rw [saturationProfile_eq_self R hR (by simpa only [abs_norm] using hz),
      div_self (norm_ne_zero_iff.mpr hzero), one_smul]

theorem saturation_eq_zero (R : ℝ) (hR : 1 ≤ R) {z : ℂ}
    (hz : R + 1 ≤ ‖z‖) : saturation R hR z = 0 := by
  simp [saturation, saturationProfile_eq_zero R hR hz]

theorem norm_saturation (R : ℝ) (hR : 1 ≤ R) (z : ℂ) :
    ‖saturation R hR z‖ = saturationProfile R hR ‖z‖ := by
  by_cases hz : z = 0
  · subst z
    simp [saturationProfile, saturationPrimitive]
  · rw [saturation, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (saturationProfile_nonneg R hR (norm_nonneg z))
        (norm_nonneg z)), div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hz)]

theorem norm_saturation_le_two (R : ℝ) (hR : 1 ≤ R) (z : ℂ) :
    ‖saturation R hR z‖ ≤ 2 := by
  rw [norm_saturation]
  exact saturationProfile_le_two R hR (norm_nonneg z)

theorem saturation_contDiff (R : ℝ) (hR : 1 ≤ R) :
    ContDiff ℝ ∞ (saturation R hR) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    apply contDiffAt_id.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with w hw
    have hw' : ‖w‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hw
    exact saturation_eq_self R hR hw'.le
  · have hn : ContDiffAt ℝ ∞ (fun w : ℂ => ‖w‖) z := contDiffAt_norm ℝ hz
    exact (((saturationProfile_contDiff R hR).contDiffAt.comp z hn).div hn
      (norm_ne_zero_iff.mpr hz)).smul contDiffAt_id

theorem saturation_hasCompactSupport (R : ℝ) (hR : 1 ≤ R) :
    HasCompactSupport (saturation R hR) := by
  apply (isCompact_closedBall (0 : ℂ) (R + 1)).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  by_contra h
  have hzR : R + 1 ≤ ‖z‖ := by
    have : ¬ ‖z‖ ≤ R + 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using h
    exact (lt_of_not_ge this).le
  exact hz (saturation_eq_zero R hR hzR)

def sphereSaturation (R : ℝ) (hR : 1 ≤ R) (z : OnePoint ℂ) : ℂ :=
  z.elim 0 (saturation R hR)

@[simp] theorem sphereSaturation_infty (R : ℝ) (hR : 1 ≤ R) :
    sphereSaturation R hR OnePoint.infty = 0 := rfl

@[simp] theorem sphereSaturation_coe (R : ℝ) (hR : 1 ≤ R) (z : ℂ) :
    sphereSaturation R hR (z : OnePoint ℂ) = saturation R hR z := rfl

theorem sphereSaturation_continuous (R : ℝ) (hR : 1 ≤ R) :
    Continuous (sphereSaturation R hR) := by
  rw [OnePoint.continuous_iff]
  refine ⟨?_, (saturation_contDiff R hR).continuous⟩
  exact tendsto_const_nhds.congr'
    (hasCompactSupport_iff_eventuallyEq.mp (saturation_hasCompactSupport R hR)).symm

theorem norm_sphereSaturation_le_two (R : ℝ) (hR : 1 ≤ R) (z : OnePoint ℂ) :
    ‖sphereSaturation R hR z‖ ≤ 2 := by
  induction z using OnePoint.rec with
  | infty => simp
  | coe z => exact norm_saturation_le_two R hR z

theorem saturation_inv_eventually_zero (R : ℝ) (hR : 1 ≤ R) :
    (fun w : ℂ => saturation R hR w⁻¹) =ᶠ[𝓝 0] 0 := by
  have hpos : 0 < R + 1 := by linarith
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (inv_pos.mpr hpos)] with w hw
  by_cases hwzero : w = 0
  · simp [hwzero]
  · apply saturation_eq_zero
    rw [norm_inv]
    have hw' : ‖w‖ < (R + 1)⁻¹ := by
      simpa only [Metric.mem_ball, dist_zero_right] using hw
    calc
      R + 1 = ((R + 1)⁻¹)⁻¹ := (inv_inv _).symm
      _ ≤ ‖w‖⁻¹ := (inv_le_inv₀ (inv_pos.mpr hpos) (norm_pos_iff.mpr hwzero)).mpr hw'.le

theorem saturation_inv_contDiff (R : ℝ) (hR : 1 ≤ R) :
    ContDiff ℝ ∞ (fun w : ℂ => saturation R hR w⁻¹) := by
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : w = 0
  · subst w
    exact contDiffAt_const.congr_of_eventuallyEq (saturation_inv_eventually_zero R hR)
  · exact (saturation_contDiff R hR).contDiffAt.comp w (contDiffAt_id.inv hw)

end Problem340

end

end OAI
