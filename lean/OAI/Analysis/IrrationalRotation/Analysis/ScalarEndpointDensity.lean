import OAI.Analysis.IrrationalRotation.Model.ScalarEndpointDensity
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarEndpointDensity

theorem endpointMap_left (t : ℝ) {z : ℝ} (hz : z ≤ 1 / 2) :
    endpointMap t z = (1 + t) * z := by
  unfold endpointMap cutDistance
  rw [min_eq_left (by linarith)]
  ring

theorem endpointMap_right (t : ℝ) {z : ℝ} (hz : 1 / 2 ≤ z) :
    endpointMap t z = (1 - t) * z + t := by
  unfold endpointMap cutDistance
  rw [min_eq_right (by linarith)]
  ring

theorem continuous_endpointMap (t : ℝ) : Continuous (endpointMap t) := by
  unfold endpointMap cutDistance
  fun_prop

theorem endpointMap_zero (t : ℝ) : endpointMap t 0 = 0 := by
  simp [endpointMap, cutDistance]

theorem endpointMap_one (t : ℝ) : endpointMap t 1 = 1 := by
  simp [endpointMap, cutDistance]

theorem endpointMap_half (t : ℝ) : endpointMap t (1 / 2) = midpoint t := by
  rw [endpointMap_left t le_rfl]
  unfold midpoint
  ring

theorem strictMono_endpointMap {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    StrictMono (endpointMap t) := by
  intro x y hxy
  by_cases hx : x ≤ 1 / 2
  · by_cases hy : y ≤ 1 / 2
    · rw [endpointMap_left t hx, endpointMap_left t hy]
      exact mul_lt_mul_of_pos_left hxy (by linarith)
    · rw [endpointMap_left t hx, endpointMap_right t (by linarith)]
      have hleft : (1 + t) * x ≤ (1 + t) * (1 / 2) :=
        mul_le_mul_of_nonneg_left hx (by linarith)
      have hright : (1 - t) * (1 / 2) < (1 - t) * y :=
        mul_lt_mul_of_pos_left (by linarith) (by linarith)
      linarith
  · rw [endpointMap_right t (by linarith), endpointMap_right t (by linarith)]
    have := mul_lt_mul_of_pos_left hxy (show 0 < 1 - t by linarith)
    linarith

theorem endpointMap_mem_unitInterval {t z : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : endpointMap t z ∈ Icc (0 : ℝ) 1 := by
  have hm := (strictMono_endpointMap ht0 ht1).monotone
  constructor
  · simpa only [endpointMap_zero] using hm hz0
  · simpa only [endpointMap_one] using hm hz1

theorem midpoint_pos {t : ℝ} (ht0 : 0 ≤ t) : 0 < midpoint t := by
  unfold midpoint
  linarith

theorem midpoint_lt_one {t : ℝ} (ht1 : t < 1) : midpoint t < 1 := by
  unfold midpoint
  linarith

theorem slopeDensity_pos {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (s : ℝ) :
    0 < slopeDensity t s := by
  unfold slopeDensity
  split_ifs <;> positivity

theorem slopeDensity_lower {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (s : ℝ) :
    (1 + t)⁻¹ ≤ slopeDensity t s := by
  unfold slopeDensity
  split_ifs
  · exact le_rfl
  · apply inv_anti₀ (by linarith)
    linarith

theorem slopeDensity_upper {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (s : ℝ) :
    slopeDensity t s ≤ (1 - t)⁻¹ := by
  unfold slopeDensity
  split_ifs
  · apply inv_anti₀ (by linarith)
    linarith
  · exact le_rfl

theorem slopeDensity_mul_intervalIntegrable {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {φ : ℝ → ℝ} (hφ : Continuous φ) :
    IntervalIntegrable (fun s => φ s * slopeDensity t s) volume 0 1 := by
  have hm0 := midpoint_pos ht0
  have hm1 := midpoint_lt_one ht1
  have hleft : IntervalIntegrable (fun s => φ s * slopeDensity t s)
      volume 0 (midpoint t) := by
    have hi : IntervalIntegrable (fun s => φ s * (1 + t)⁻¹)
        volume 0 (midpoint t) := (hφ.mul continuous_const).intervalIntegrable _ _
    apply hi.congr_uIoo
    intro s hs
    rw [uIoo_of_le hm0.le] at hs
    simp only [slopeDensity, ite_eq_left hs.2.le]
  have hright : IntervalIntegrable (fun s => φ s * slopeDensity t s)
      volume (midpoint t) 1 := by
    have hi : IntervalIntegrable (fun s => φ s * (1 - t)⁻¹)
        volume (midpoint t) 1 := (hφ.mul continuous_const).intervalIntegrable _ _
    apply hi.congr_uIoo
    intro s hs
    rw [uIoo_of_le hm1.le] at hs
    simp only [slopeDensity, ite_eq_right (not_le_of_gt hs.1)]
  exact hleft.trans hright

theorem endpointMap_integral {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {φ : ℝ → ℝ} (hφ : Continuous φ) :
    (∫ z in (0 : ℝ)..1, φ (endpointMap t z)) =
      ∫ s in (0 : ℝ)..1, φ s * slopeDensity t s := by
  have hp : 1 + t ≠ 0 := ne_of_gt (by linarith)
  have hn : 1 - t ≠ 0 := ne_of_gt (by linarith)
  have hm0 := midpoint_pos ht0
  have hm1 := midpoint_lt_one ht1
  have hc : Continuous (fun z => φ (endpointMap t z)) :=
    hφ.comp (continuous_endpointMap t)
  have hleft : (∫ z in (0 : ℝ)..(1 / 2), φ (endpointMap t z)) =
      (1 + t)⁻¹ * ∫ s in (0 : ℝ)..midpoint t, φ s := by
    calc
      _ = ∫ z in (0 : ℝ)..(1 / 2), φ ((1 + t) * z) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro z hz
        dsimp
        rw [endpointMap_left t hz.2.le]
      _ = _ := by
        rw [intervalIntegral.integral_comp_mul_left φ hp]
        simp only [mul_zero, smul_eq_mul]
        congr 2
        unfold midpoint
        ring
  have hright : (∫ z in (1 / 2 : ℝ)..1, φ (endpointMap t z)) =
      (1 - t)⁻¹ * ∫ s in midpoint t..(1 : ℝ), φ s := by
    calc
      _ = ∫ z in (1 / 2 : ℝ)..1, φ ((1 - t) * z + t) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro z hz
        dsimp
        rw [endpointMap_right t hz.1.le]
      _ = _ := by
        rw [intervalIntegral.integral_comp_mul_add φ hn t]
        simp only [smul_eq_mul]
        congr 2
        · unfold midpoint
          ring
        · ring
  have hd := slopeDensity_mul_intervalIntegrable ht0 ht1 hφ
  have hdleft : (∫ s in (0 : ℝ)..midpoint t, φ s * slopeDensity t s) =
      (1 + t)⁻¹ * ∫ s in (0 : ℝ)..midpoint t, φ s := by
    calc
      _ = ∫ s in (0 : ℝ)..midpoint t, φ s * (1 + t)⁻¹ := by
        apply intervalIntegral.integral_congr_Ioo_of_le hm0.le
        intro s hs
        simp only [slopeDensity, ite_eq_left hs.2.le]
      _ = _ := by rw [intervalIntegral.integral_mul_const]; ring
  have hdright : (∫ s in midpoint t..(1 : ℝ), φ s * slopeDensity t s) =
      (1 - t)⁻¹ * ∫ s in midpoint t..(1 : ℝ), φ s := by
    calc
      _ = ∫ s in midpoint t..(1 : ℝ), φ s * (1 - t)⁻¹ := by
        apply intervalIntegral.integral_congr_Ioo_of_le hm1.le
        intro s hs
        simp only [slopeDensity, ite_eq_right (not_le_of_gt hs.1)]
      _ = _ := by rw [intervalIntegral.integral_mul_const]; ring
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 (1 / 2)) (hc.intervalIntegrable (1 / 2) 1), hleft, hright]
  have hdl : IntervalIntegrable (fun s => φ s * slopeDensity t s)
      volume 0 (midpoint t) := hd.mono_set (by
    rw [uIcc_of_le hm0.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hm1.le)
  have hdr : IntervalIntegrable (fun s => φ s * slopeDensity t s)
      volume (midpoint t) 1 := hd.mono_set (by
    rw [uIcc_of_le hm1.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc hm0.le le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hdl hdr]
  rw [hdleft, hdright]

theorem integral_slopeDensity {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (∫ s in (0 : ℝ)..1, slopeDensity t s) = 1 := by
  have h := endpointMap_integral ht0 ht1 (φ := fun _ => 1) continuous_const
  simpa using h.symm

theorem slopeDensity_deviation {t h : ℝ} (ht0 : 0 ≤ t) (hth : t ≤ h)
    (hh1 : h < 1) (s : ℝ) :
    |slopeDensity t s - 1| ≤ h / (1 - h) := by
  have ht1 : t < 1 := lt_of_le_of_lt hth hh1
  have hh0 : 0 ≤ h := le_trans ht0 hth
  have hp : 0 < 1 + t := by linarith
  have hn : 0 < 1 - t := by linarith
  have hd : 0 < 1 - h := by linarith
  unfold slopeDensity
  split_ifs
  · have heq : (1 + t)⁻¹ - 1 = -(t / (1 + t)) := by
      field_simp
      ring
    rw [heq, abs_neg, abs_of_nonneg (div_nonneg ht0 hp.le)]
    exact div_le_div₀ hh0 hth hd (by linarith)
  · have heq : (1 - t)⁻¹ - 1 = t / (1 - t) := by
      field_simp
      ring
    rw [heq, abs_of_nonneg (div_nonneg ht0 hn.le)]
    exact div_le_div₀ hh0 hth hd (by linarith)

theorem slopeDensity_uniform_upper {t h : ℝ} (ht0 : 0 ≤ t) (hth : t ≤ h)
    (hh1 : h < 1) (s : ℝ) : slopeDensity t s ≤ (1 - h)⁻¹ := by
  apply (slopeDensity_upper ht0 (lt_of_le_of_lt hth hh1) s).trans
  exact inv_anti₀ (by linarith) (by linarith)

theorem measurable_slopeDensity : Measurable (fun p : ℝ × ℝ => slopeDensity p.1 p.2) := by
  unfold slopeDensity midpoint
  apply Measurable.ite
  · exact measurableSet_le measurable_snd
      ((measurable_const.add measurable_fst).div_const 2)
  · exact (measurable_const.add measurable_fst).inv
  · exact (measurable_const.sub measurable_fst).inv

theorem slopeDensity_parameter_integrable {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h < 1)
    (s : ℝ) : IntervalIntegrable (fun t => slopeDensity t s) volume 0 h := by
  rw [intervalIntegrable_iff]
  apply IntegrableOn.of_bound (by rw [uIoc_of_le hh0]; exact measure_Ioc_lt_top)
    ((measurable_slopeDensity.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    ((1 - h)⁻¹)
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [uIoc_of_le hh0] at ht
  change ‖slopeDensity t s‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos (slopeDensity_pos ht.1.le (lt_of_le_of_lt ht.2 hh1) s)]
  exact slopeDensity_uniform_upper ht.1.le ht.2 hh1 s

theorem averagedDensity_nonneg {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) (s : ℝ) :
    0 ≤ averagedDensity h s := by
  unfold averagedDensity
  apply mul_nonneg (inv_nonneg.mpr hh0.le)
  apply intervalIntegral.integral_nonneg hh0.le
  intro t ht
  exact (slopeDensity_pos ht.1 (lt_of_le_of_lt ht.2 hh1) s).le

theorem averagedDensity_upper {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) (s : ℝ) :
    averagedDensity h s ≤ (1 - h)⁻¹ := by
  have hint := slopeDensity_parameter_integrable hh0.le hh1 s
  have hb : (∫ t in (0 : ℝ)..h, slopeDensity t s) ≤ h * (1 - h)⁻¹ := by
    calc
      _ ≤ ∫ _t in (0 : ℝ)..h, (1 - h)⁻¹ :=
        intervalIntegral.integral_mono_on hh0.le hint intervalIntegrable_const
          (fun t ht => slopeDensity_uniform_upper ht.1 ht.2 hh1 s)
      _ = _ := by simp
  unfold averagedDensity
  calc
    _ ≤ h⁻¹ * (h * (1 - h)⁻¹) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hh0.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hh0.ne', one_mul]

theorem averagedDensity_deviation {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) (s : ℝ) :
    |averagedDensity h s - 1| ≤ h / (1 - h) := by
  have hint := slopeDensity_parameter_integrable hh0.le hh1 s
  have heq : averagedDensity h s - 1 =
      h⁻¹ * ∫ t in (0 : ℝ)..h, (slopeDensity t s - 1) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
    unfold averagedDensity
    rw [mul_sub, inv_mul_cancel₀ hh0.ne']
  rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hh0)]
  have hb : |∫ t in (0 : ℝ)..h, (slopeDensity t s - 1)| ≤
      (h / (1 - h)) * h := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := h) (C := h / (1 - h))
      (f := fun t => slopeDensity t s - 1) (by
        intro t ht
        rw [uIoc_of_le hh0.le] at ht
        simpa only [Real.norm_eq_abs] using slopeDensity_deviation ht.1.le ht.2 hh1 s)
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos hh0] using this
  calc
    _ ≤ h⁻¹ * ((h / (1 - h)) * h) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hh0.le)
    _ = _ := by field_simp

theorem slopeDensity_rectangle_integrable {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h < 1) :
    IntegrableOn (Function.uncurry slopeDensity)
      (uIoc (0 : ℝ) h ×ˢ uIoc (0 : ℝ) 1) := by
  have hfinite : volume (uIoc (0 : ℝ) h ×ˢ uIoc (0 : ℝ) 1) < ⊤ := by
    apply lt_of_le_of_lt (measure_mono (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc))
    exact (isCompact_uIcc.prod isCompact_uIcc).measure_lt_top
  apply IntegrableOn.of_bound hfinite measurable_slopeDensity.aestronglyMeasurable ((1 - h)⁻¹)
  filter_upwards [ae_restrict_mem (measurableSet_uIoc.prod measurableSet_uIoc)] with p hp
  have ht := hp.1
  rw [uIoc_of_le hh0] at ht
  change ‖slopeDensity p.1 p.2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos (slopeDensity_pos ht.1.le (lt_of_le_of_lt ht.2 hh1) p.2)]
  exact slopeDensity_uniform_upper ht.1.le ht.2 hh1 p.2

theorem averagedDensity_intervalIntegrable {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    IntervalIntegrable (averagedDensity h) volume 0 1 := by
  have hr := slopeDensity_rectangle_integrable hh0.le hh1
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hr
  have hi := hr.integral_prod_right.const_mul h⁻¹
  rw [intervalIntegrable_iff]
  change Integrable (fun s => h⁻¹ * ∫ t in (0 : ℝ)..h, slopeDensity t s)
    (volume.restrict (uIoc (0 : ℝ) 1))
  simpa only [intervalIntegral.integral_of_le hh0.le,
    uIoc_of_le hh0.le, Function.uncurry] using hi

theorem integral_averagedDensity {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    (∫ s in (0 : ℝ)..1, averagedDensity h s) = 1 := by
  have hr := slopeDensity_rectangle_integrable hh0.le hh1
  have hi : (∫ t in (0 : ℝ)..h, ∫ s in (0 : ℝ)..1, slopeDensity t s) = h := by
    calc
      _ = ∫ _t in (0 : ℝ)..h, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hh0.le
        intro t ht
        exact integral_slopeDensity ht.1.le (lt_trans ht.2 hh1)
      _ = _ := by simp
  unfold averagedDensity
  rw [intervalIntegral.integral_const_mul,
    ← intervalIntegral_intervalIntegral_swap hr, hi, inv_mul_cancel₀ hh0.ne']

theorem unitMass_square_identity {f : ℝ → ℝ} {δ : ℝ}
    (hf : IntervalIntegrable f volume 0 1) (hδ : 0 ≤ δ)
    (hbound : ∀ s ∈ Icc (0 : ℝ) 1, |f s - 1| ≤ δ)
    (hmass : (∫ s in (0 : ℝ)..1, f s) = 1) :
    (∫ s in (0 : ℝ)..1, (f s) ^ 2) =
      1 + ∫ s in (0 : ℝ)..1, (f s - 1) ^ 2 := by
  have hdev : IntervalIntegrable (fun s => (f s - 1) ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff]
    apply IntegrableOn.of_bound (by simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact measure_Ioc_lt_top)
      ((hf.def'.aestronglyMeasurable.sub aestronglyMeasurable_const).pow 2) (δ ^ 2)
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    have hb := hbound s ⟨hs.1.le, hs.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (f s - 1) ^ 2 ≤ δ ^ 2
    exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hδ] using hb)
  have hfun : (fun s => (f s) ^ 2) =
      (fun s => (f s - 1) ^ 2 + 2 * f s - 1) := by
    funext s
    ring
  rw [hfun, intervalIntegral.integral_sub (hdev.add (hf.const_mul 2)) intervalIntegrable_const,
    intervalIntegral.integral_add hdev (hf.const_mul 2), intervalIntegral.integral_const_mul, hmass]
  simp
  ring

theorem unitMass_square_le {f : ℝ → ℝ} {δ : ℝ}
    (hf : IntervalIntegrable f volume 0 1) (hδ : 0 ≤ δ)
    (hbound : ∀ s ∈ Icc (0 : ℝ) 1, |f s - 1| ≤ δ)
    (hmass : (∫ s in (0 : ℝ)..1, f s) = 1) :
    (∫ s in (0 : ℝ)..1, (f s) ^ 2) ≤ 1 + δ ^ 2 := by
  rw [unitMass_square_identity hf hδ hbound hmass]
  apply add_le_add le_rfl
  have hint : IntervalIntegrable (fun s => (f s - 1) ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff]
    apply IntegrableOn.of_bound (by simp only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact measure_Ioc_lt_top)
      ((hf.def'.aestronglyMeasurable.sub aestronglyMeasurable_const).pow 2) (δ ^ 2)
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    have hb := hbound s ⟨hs.1.le, hs.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (f s - 1) ^ 2 ≤ δ ^ 2
    exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hδ] using hb)
  calc
    _ ≤ ∫ _s in (0 : ℝ)..1, δ ^ 2 :=
      intervalIntegral.integral_mono_on (by norm_num) hint intervalIntegrable_const
        (fun s hs => by
          have hb := hbound s hs
          exact sq_le_sq.mpr (by simpa only [abs_of_nonneg hδ] using hb))
    _ = _ := by simp

theorem averagedDensity_second_moment {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1) :
    (∫ s in (0 : ℝ)..1, (averagedDensity h s) ^ 2) ≤
      1 + h ^ 2 / (1 - h) ^ 2 := by
  have hb := unitMass_square_le (averagedDensity_intervalIntegrable hh0 hh1)
    (show 0 ≤ h / (1 - h) by positivity)
    (fun s _ => averagedDensity_deviation hh0 hh1 s)
    (integral_averagedDensity hh0 hh1)
  simpa only [div_pow] using hb

end Invariant233.ScalarEndpointDensity

end OAI
