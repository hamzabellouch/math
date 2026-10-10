import OAI.Geometry.Riemannian.HarmonicCore.WarpProfiles

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution
open Matrix
open scoped RealInnerProductSpace

namespace HarmonicCounterexample
lemma tailDensity_zero {J t : ℝ} (hJ : 0 < J) (ht : t ≤ J / 2) :
    tailDensity J t = 0 := by
  unfold tailDensity
  rw [theta_zero]
  · simp
  · apply (div_le_iff₀ hJ).2
    linarith

lemma tailDensity_nonneg {J : ℝ} (hJ : 0 < J) (t : ℝ) :
    0 ≤ tailDensity J t := by
  by_cases ht : t ≤ J / 2
  · rw [tailDensity_zero hJ ht]
  · exact mul_nonneg (theta_nonneg _) (Real.rpow_nonneg (by linarith) _)

lemma tailDensity_le {J t : ℝ} (ht : 0 ≤ t) :
    tailDensity J t ≤ t ^ (-(3 / 2 : ℝ)) := by
  exact mul_le_of_le_one_left (Real.rpow_nonneg ht _) (theta_le_one _)

lemma tailDensity_exact {J t : ℝ} (hJ : 0 < J) (ht : 7 / 10 * J ≤ t) :
    tailDensity J t = t ^ (-(3 / 2 : ℝ)) := by
  unfold tailDensity
  rw [theta_one]
  · simp
  · exact (le_div_iff₀ hJ).2 ht

lemma tailDensity_smooth {J : ℝ} (hJ : 0 < J) :
    ContDiff ℝ ∞ (tailDensity J) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : 0 < t
  · exact ((theta_smooth.comp (contDiff_id.div_const J)).contDiffAt).mul
      (Real.contDiffAt_rpow_const_of_ne (ne_of_gt ht))
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds (show t < J / 2 by linarith)] with v hv
    exact tailDensity_zero hJ hv.le

lemma tailDensity_integrable {J : ℝ} (hJ : 0 < J) :
    IntegrableOn (tailDensity J) (Ioi (J / 2)) := by
  apply (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3/2 : ℝ) < -1)
    (show 0 < J / 2 by positivity)).mono'
  · exact (tailDensity_smooth hJ).continuous.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (tailDensity_nonneg hJ t)]
    exact tailDensity_le (by have := ht; simp only [mem_Ioi] at this; linarith)

lemma tailMass_nonneg {J : ℝ} (hJ : 0 < J) : 0 ≤ tailMass J := by
  exact integral_nonneg (fun t ↦ tailDensity_nonneg hJ t)

lemma tailMass_bound {J : ℝ} (hJ : 0 < J) :
    tailMass J ≤ 2 * (J / 2) ^ (-(1/2 : ℝ)) := by
  have hp : 0 < J / 2 := by positivity
  have h := setIntegral_mono_on (tailDensity_integrable hJ)
    (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3/2 : ℝ) < -1) hp)
    measurableSet_Ioi (fun t ht ↦ tailDensity_le (le_of_lt (hp.trans ht)))
  rw [integral_Ioi_rpow_of_lt (by norm_num : -(3/2 : ℝ) < -1) hp] at h
  norm_num at h
  simpa [tailMass, div_eq_mul_inv, mul_comm] using h

lemma tailPrimitive_hasDerivAt {J : ℝ} (hJ : 0 < J) (t : ℝ) :
    HasDerivAt (tailPrimitive J) (tailDensity J t) t := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((tailDensity_smooth hJ).continuous.intervalIntegrable _ _)
    ((tailDensity_smooth hJ).continuous.stronglyMeasurableAtFilter _ _)
    (tailDensity_smooth hJ).continuous.continuousAt

lemma tailPrimitive_deriv {J : ℝ} (hJ : 0 < J) :
    deriv (tailPrimitive J) = tailDensity J := by
  funext t
  exact (tailPrimitive_hasDerivAt hJ t).deriv

lemma tailPrimitive_smooth {J : ℝ} (hJ : 0 < J) :
    ContDiff ℝ ∞ (tailPrimitive J) := by
  rw [contDiff_infty_iff_deriv, tailPrimitive_deriv hJ]
  exact ⟨fun t ↦ (tailPrimitive_hasDerivAt hJ t).differentiableAt,
    tailDensity_smooth hJ⟩

lemma tailPrimitive_zero {J t : ℝ} (hJ : 0 < J) (ht : t ≤ J / 2) :
    tailPrimitive J t = 0 := by
  unfold tailPrimitive
  calc
    (∫ v in (0 : ℝ)..t, tailDensity J v) = ∫ v in (0 : ℝ)..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro v hv
      exact tailDensity_zero hJ (hv.2.trans (max_le (by linarith) ht))
    _ = 0 := by simp

lemma tailPrimitive_nonneg {J : ℝ} (hJ : 0 < J) (t : ℝ) :
    0 ≤ tailPrimitive J t := by
  by_cases ht : 0 ≤ t
  · exact intervalIntegral.integral_nonneg_of_forall ht (tailDensity_nonneg hJ)
  · rw [tailPrimitive_zero hJ (by linarith)]

lemma tail_decomposition {J t : ℝ} (hJ : 0 < J) (ht : J / 2 ≤ t) :
    tailPrimitive J t + (∫ v in Ioi t, tailDensity J v) = tailMass J := by
  have hs := intervalIntegral.integral_add_adjacent_intervals
    ((tailDensity_smooth hJ).continuous.intervalIntegrable (μ := volume) 0 (J / 2))
    ((tailDensity_smooth hJ).continuous.intervalIntegrable (μ := volume) (J / 2) t)
  have h0 := tailPrimitive_zero hJ (le_refl (J / 2))
  have hf := intervalIntegral.integral_interval_add_Ioi (tailDensity_integrable hJ)
    ((tailDensity_integrable hJ).mono_set (Ioi_subset_Ioi ht))
  dsimp [tailPrimitive, tailMass] at *
  linarith

lemma tailPrimitive_le_mass {J : ℝ} (hJ : 0 < J) (t : ℝ) :
    tailPrimitive J t ≤ tailMass J := by
  by_cases ht : t ≤ J / 2
  · rw [tailPrimitive_zero hJ ht]
    exact tailMass_nonneg hJ
  · have hn : 0 ≤ ∫ v in Ioi t, tailDensity J v :=
      integral_nonneg (tailDensity_nonneg hJ)
    linarith [tail_decomposition hJ (le_of_not_ge ht)]

lemma tailPrimitive_exact {J t : ℝ} (hJ : 0 < J) (ht : 7 / 10 * J ≤ t) :
    tailPrimitive J t = tailMass J - 2 * t ^ (-(1/2 : ℝ)) := by
  have htpos : 0 < t := by linarith
  have heq : (∫ v in Ioi t, tailDensity J v) = ∫ v in Ioi t, v ^ (-(3/2 : ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    exact tailDensity_exact hJ (ht.trans hv.le)
  have hd := tail_decomposition hJ (show J / 2 ≤ t by linarith)
  rw [heq, integral_Ioi_rpow_of_lt (by norm_num : -(3/2 : ℝ) < -1) htpos] at hd
  norm_num at hd
  have hn : t ^ (-(1/2 : ℝ)) / (1/2 : ℝ) = 2 * t ^ (-(1/2 : ℝ)) := by ring
  rw [hn] at hd
  linarith

lemma radialPrimitive_zero {J r : ℝ} (hJ : 0 < J) (hr : r ≤ Real.exp (J / 2)) :
    radialPrimitive J r = 0 := by
  unfold radialPrimitive
  split_ifs with h
  · rfl
  · apply tailPrimitive_zero hJ
    exact (Real.log_le_iff_le_exp (by linarith)).2 hr

lemma radialPrimitive_smooth {J : ℝ} (hJ : 0 < J) :
    ContDiff ℝ ∞ (radialPrimitive J) := by
  rw [contDiff_iff_contDiffAt]
  intro r
  by_cases hr : r < Real.exp (J / 2)
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hr] with x hx
    exact radialPrimitive_zero hJ hx.le
  · have h1 : 1 < r := lt_of_lt_of_le (by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)) (le_of_not_gt hr)
    apply ((tailPrimitive_smooth hJ).contDiffAt.comp r
      (Real.contDiffAt_log.mpr (ne_of_gt (show 0 < r by linarith)))).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds h1] with x hx
    simp only [radialPrimitive, not_le.mpr hx, ↓reduceIte, Function.comp_def]

lemma radialPrimitive_nonneg {J : ℝ} (hJ : 0 < J) (r : ℝ) :
    0 ≤ radialPrimitive J r := by
  unfold radialPrimitive
  split_ifs
  · rfl
  · exact tailPrimitive_nonneg hJ _

lemma radialPrimitive_le_mass {J : ℝ} (hJ : 0 < J) (r : ℝ) :
    radialPrimitive J r ≤ tailMass J := by
  unfold radialPrimitive
  split_ifs
  · exact tailMass_nonneg hJ
  · exact tailPrimitive_le_mass hJ _

lemma slope_smooth {C J : ℝ} (hJ : 0 < J) :
    ContDiff ℝ ∞ (slope C J) := by
  exact (contDiff_const.sub (contDiff_const.mul sigma_smooth)).sub
    (contDiff_const.mul (radialPrimitive_smooth hJ))

lemma slope_le_one {C J : ℝ} (hJ : 0 < J) (hC : 0 ≤ C)
    (hm : 0 ≤ compactLoss C J) (r : ℝ) : slope C J r ≤ 1 := by
  have h1 := mul_nonneg hm (sigma_nonneg r)
  have h2 := mul_nonneg hC (radialPrimitive_nonneg hJ r)
  dsimp [slope]
  linarith

lemma a_le_slope {C J : ℝ} (hJ : 0 < J) (hC : 0 ≤ C)
    (hm : 0 ≤ compactLoss C J) (r : ℝ) : a ≤ slope C J r := by
  have h1 := mul_le_mul_of_nonneg_left (sigma_le_one r) hm
  have h2 := mul_le_mul_of_nonneg_left (radialPrimitive_le_mass hJ r) hC
  dsimp [slope, compactLoss] at *
  linarith

lemma slope_one_near_zero {C J r : ℝ} (hr : r ≤ 1) : slope C J r = 1 := by
  simp only [slope, radialPrimitive, hr, ↓reduceIte, sigma_zero (by linarith : r ≤ 5/4)]
  ring

lemma warping_hasDerivAt {C J : ℝ} (hJ : 0 < J) (r : ℝ) :
    HasDerivAt (warping C J) (slope C J r) r := by
  exact intervalIntegral.integral_hasDerivAt_right
    ((slope_smooth hJ).continuous.intervalIntegrable _ _)
    ((slope_smooth hJ).continuous.stronglyMeasurableAtFilter _ _)
    (slope_smooth hJ).continuous.continuousAt

lemma warping_deriv {C J : ℝ} (hJ : 0 < J) :
    deriv (warping C J) = slope C J := by
  funext r
  exact (warping_hasDerivAt hJ r).deriv

lemma warping_smooth {C J : ℝ} (hJ : 0 < J) :
    ContDiff ℝ ∞ (warping C J) := by
  rw [contDiff_infty_iff_deriv, warping_deriv hJ]
  exact ⟨fun r ↦ (warping_hasDerivAt hJ r).differentiableAt, slope_smooth hJ⟩

lemma warping_eq_id_near_zero {C J r : ℝ} (hr : r ≤ 1) : warping C J r = r := by
  unfold warping
  calc
    (∫ x in (0 : ℝ)..r, slope C J x) = ∫ x in (0 : ℝ)..r, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro v hv
      exact slope_one_near_zero (hv.2.trans (max_le (by norm_num) hr))
    _ = r := by simp

def radialDensity (J r : ℝ) : ℝ :=
  if Real.exp (J / 2) < r then tailDensity J (Real.log r) / r else 0

lemma radialPrimitive_hasDerivAt_gt_one {J r : ℝ} (hJ : 0 < J) (hr : 1 < r) :
    HasDerivAt (radialPrimitive J) (tailDensity J (Real.log r) / r) r := by
  have hd := (tailPrimitive_hasDerivAt hJ (Real.log r)).comp r
    (Real.hasDerivAt_log (by linarith : r ≠ 0))
  simp only [div_eq_mul_inv]
  apply hd.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hr] with x hx
  simp only [radialPrimitive, not_le.mpr hx, ↓reduceIte, Function.comp_def]

lemma radialPrimitive_hasDerivAt {J : ℝ} (hJ : 0 < J) (r : ℝ) :
    HasDerivAt (radialPrimitive J) (radialDensity J r) r := by
  have he : 1 < Real.exp (J / 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  by_cases hr : 1 < r
  · have hd := radialPrimitive_hasDerivAt_gt_one hJ hr
    unfold radialDensity
    split_ifs with h
    · exact hd
    · have hz := tailDensity_zero hJ
        ((Real.log_le_iff_le_exp (by linarith : 0 < r)).2 (le_of_not_gt h))
      simpa only [hz, zero_div] using hd
  · have hrcut : r < Real.exp (J / 2) := (le_of_not_gt hr).trans_lt he
    have hz : radialDensity J r = 0 := by
      simp only [radialDensity, not_lt.mpr hrcut.le, ↓reduceIte]
    rw [hz]
    apply (hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hrcut] with x hx
    exact radialPrimitive_zero hJ hx.le

lemma radialDensity_nonneg {J : ℝ} (hJ : 0 < J) (r : ℝ) :
    0 ≤ radialDensity J r := by
  unfold radialDensity
  split_ifs with hr
  · exact div_nonneg (tailDensity_nonneg hJ _) (le_of_lt ((Real.exp_pos _).trans hr))
  · rfl

lemma slope_hasDerivAt {C J : ℝ} (hJ : 0 < J) (r : ℝ) :
    HasDerivAt (slope C J)
      (-compactLoss C J * beta r - C * radialDensity J r) r := by
  have hsig := (sigma_smooth.differentiable (by simp) r).hasDerivAt
  have hd := ((hasDerivAt_const r (1 : ℝ)).sub
    (hsig.const_mul (compactLoss C J))).sub ((radialPrimitive_hasDerivAt hJ r).const_mul C)
  convert hd using 1 <;> try rfl
  simp only [beta, zero_sub, neg_mul]

lemma warping_second_deriv {C J : ℝ} (hJ : 0 < J) (r : ℝ) :
    deriv (deriv (warping C J)) r =
      -compactLoss C J * beta r - C * radialDensity J r := by
  rw [warping_deriv hJ]
  exact (slope_hasDerivAt hJ r).deriv

lemma slope_antitone {C J : ℝ} (hJ : 0 < J) (hC : 0 ≤ C)
    (hm : 0 ≤ compactLoss C J) : Antitone (slope C J) := by
  apply antitone_of_deriv_nonpos ((slope_smooth hJ).differentiable (by simp))
  intro r
  rw [(slope_hasDerivAt hJ r).deriv]
  have h1 := mul_nonneg hm (beta_nonneg r)
  have h2 := mul_nonneg hC (radialDensity_nonneg hJ r)
  linarith

lemma warping_bounds {C J r : ℝ} (hJ : 0 < J) (hC : 0 ≤ C)
    (hm : 0 ≤ compactLoss C J) (hr : 0 ≤ r) :
    a * r ≤ warping C J r ∧ warping C J r ≤ r := by
  have hi := (slope_smooth (C := C) hJ).continuous.intervalIntegrable (μ := volume) 0 r
  constructor
  · have h := intervalIntegral.integral_mono_on hr (intervalIntegrable_const) hi
      (fun x _ ↦ a_le_slope hJ hC hm x)
    simpa [warping, mul_comm] using h
  · have h := intervalIntegral.integral_mono_on hr hi (intervalIntegrable_const)
      (fun x _ ↦ slope_le_one hJ hC hm x)
    simpa [warping, mul_comm] using h

lemma warping_pos {C J r : ℝ} (hJ : 0 < J) (hC : 0 ≤ C)
    (hm : 0 ≤ compactLoss C J) (hr : 0 < r) : 0 < warping C J r := by
  exact (mul_pos (by norm_num [a]) hr).trans_le (warping_bounds hJ hC hm hr.le).1

end HarmonicCounterexample

end

end OAI
