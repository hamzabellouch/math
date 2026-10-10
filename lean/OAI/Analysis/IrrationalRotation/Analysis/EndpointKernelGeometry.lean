import OAI.Analysis.IrrationalRotation.Sampling.ScalarSampling
import OAI.Analysis.IrrationalRotation.Analysis.ScalarEndpointDensity

namespace OAI

open MeasureTheory Set

namespace Invariant233.ScalarSampling

theorem rawKernel_uncut_zero_of_nonpos {h x v : ℝ} (hh : 0 ≤ h)
    (hx : x ≤ 0) (_hv : 0 ≤ v) : rawKernel h 0 x v = 0 := by
  unfold rawKernel
  split_ifs with hd
  · apply Set.indicator_of_notMem
    intro hmem
    have hdelta : delta x ≤ 0 := (min_le_left _ _).trans hx
    have : h * delta x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hh hdelta
    linarith [hmem.1, hmem.2]
  · rfl

theorem uncut_endpoint_no_wrap {h s v : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hs0 : 0 < s) (hs1 : s < 1) (hv0 : 0 < v) (hv1 : v < 1) :
    circleKernel h 0 (s - v) v = rawKernel h 0 (s - v) v := by
  unfold circleKernel
  rw [Int.fract_eq_self.mpr ⟨hv0.le, hv1⟩]
  by_cases hvs : v ≤ s
  · rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  · have hsv : s < v := lt_of_not_ge hvs
    rw [rawKernel_uncut_zero_of_nonpos (x := s - v) hh0 (by linarith) hv0.le]
    have hfloor : ⌊s - v⌋ = -1 := by
      apply Int.floor_eq_iff.mpr
      norm_num
      constructor <;> linarith
    have hfract : Int.fract (s - v) = s - v + 1 := by
      rw [Int.fract, hfloor]
      norm_num
    rw [hfract]
    unfold rawKernel
    split_ifs
    · apply Set.indicator_of_notMem
      intro hmem
      have hdelta0 : 0 ≤ delta (s - v + 1) := by
        apply delta_nonneg
        constructor <;> linarith
      have hdelta : delta (s - v + 1) ≤ v - s := by
        unfold delta
        exact (min_le_right _ _).trans (by linarith)
      have hmul : h * delta (s - v + 1) ≤ delta (s - v + 1) :=
        (mul_le_mul_of_nonneg_right hh1 hdelta0).trans_eq (one_mul _)
      linarith [hmem.2]
    · rfl

theorem rawKernel_le_uncut {h α s v : ℝ} (hh : 0 ≤ h)
    (hs : s ∈ Icc (0 : ℝ) 1) : rawKernel h α s v ≤ rawKernel h 0 s v := by
  have hd : 0 ≤ delta s := delta_nonneg hs
  unfold rawKernel
  rw [ite_eq_left hd]
  split_ifs
  · exact le_rfl
  · exact Set.indicator_nonneg (fun _ _ => inv_nonneg.mpr (mul_nonneg hh hd)) _

theorem uncut_endpoint_left_formula {h s : ℝ} (hh0 : 0 < h)
    (hs0 : 0 < s) (hs1 : s ≤ 1 / 2) (v : ℝ) :
    rawKernel h 0 (s - v) v =
      (Ioo 0 (h * s / (1 + h))).indicator (fun v => (h * (s - v))⁻¹) v := by
  have hp : 0 < 1 + h := by linarith
  have heq : v < h * (s - v) ↔ v < h * s / (1 + h) := by
    rw [lt_div_iff₀ hp]
    constructor <;> intro hineq <;> nlinarith
  by_cases hv : 0 < v
  · have hd : delta (s - v) = s - v := by
      unfold delta
      rw [min_eq_left (by linarith)]
    unfold rawKernel
    rw [hd]
    by_cases hvs : v < h * s / (1 + h)
    · have hvbound : v < s := by
        have := heq.mpr hvs
        nlinarith
      simp only [ite_eq_left (show 0 ≤ s - v by linarith), Set.indicator_apply, mem_Ioo,
        hv, heq.mpr hvs, hvs, and_self, ite_true]
    · have hvnot : ¬ v < h * (s - v) := fun h => hvs (heq.mp h)
      simp only [Set.indicator_apply, mem_Ioo, hv, hvnot, hvs, and_false, ite_false,
        ite_self]
  · unfold rawKernel
    simp only [Set.indicator_apply, mem_Ioo, hv, false_and, ite_false, ite_self]

theorem integral_uncut_endpoint_left {h s : ℝ} (hh0 : 0 < h)
    (hs0 : 0 < s) (hs1 : s ≤ 1 / 2) :
    (∫ v in (0 : ℝ)..1, rawKernel h 0 (s - v) v) = h⁻¹ * Real.log (1 + h) := by
  have hp : 0 < 1 + h := by linarith
  have hL0 : 0 < h * s / (1 + h) := div_pos (mul_pos hh0 hs0) hp
  have hLs : h * s / (1 + h) < s := by
    rw [div_lt_iff₀ hp]
    nlinarith
  have hL1 : h * s / (1 + h) < 1 := by linarith
  have hfun : (fun v => rawKernel h 0 (s - v) v) =
      (Ioo 0 (h * s / (1 + h))).indicator (fun v => (h * (s - v))⁻¹) := by
    funext v
    exact uncut_endpoint_left_formula hh0 hs0 hs1 v
  rw [hfun, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hL0.le]
    simp_rw [mul_inv]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left (fun z : ℝ => z⁻¹) s]
    simp only [sub_zero]
    rw [integral_inv_of_pos (by linarith : 0 < s - h * s / (1 + h)) hs0]
    have hratio : s / (s - h * s / (1 + h)) = 1 + h := by
      field_simp
      ring
    rw [hratio]
  · intro v hv
    apply Set.indicator_of_notMem
    intro hmem
    exact hv ⟨hmem.1, hmem.2.le.trans hL1.le⟩

theorem averagedDensity_left_formula {h s : ℝ} (hh0 : 0 < h) (hs1 : s ≤ 1 / 2) :
    ScalarEndpointDensity.averagedDensity h s = h⁻¹ * Real.log (1 + h) := by
  have hp : 0 < 1 + h := by linarith
  unfold ScalarEndpointDensity.averagedDensity
  congr 1
  calc
    _ = ∫ t in (0 : ℝ)..h, (1 + t)⁻¹ := by
      apply intervalIntegral.integral_congr_Ioo_of_le hh0.le
      intro t ht
      simp only [ScalarEndpointDensity.slopeDensity,
        ite_eq_left (show s ≤ ScalarEndpointDensity.midpoint t by
          unfold ScalarEndpointDensity.midpoint
          linarith [ht.1])]
    _ = Real.log (1 + h) := by
      rw [intervalIntegral.integral_comp_add_left (fun t : ℝ => t⁻¹) 1]
      simp only [add_zero]
      rw [integral_inv_of_pos (by norm_num : (0 : ℝ) < 1) hp]
      simp

theorem integral_uncut_circleEndpoint_left {h s : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hs0 : 0 < s) (hs1 : s ≤ 1 / 2) :
    (∫ v in (0 : ℝ)..1, circleKernel h 0 (s - v) v) =
      ScalarEndpointDensity.averagedDensity h s := by
  rw [averagedDensity_left_formula hh0 hs1]
  calc
    _ = ∫ v in (0 : ℝ)..1, rawKernel h 0 (s - v) v := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro v hv
      exact uncut_endpoint_no_wrap hh0.le hh1 hs0 (by linarith) hv.1 hv.2
    _ = _ := integral_uncut_endpoint_left hh0 hs0 hs1

theorem uncut_endpoint_right_formula {h s : ℝ} (hh0 : 0 < h) (_hh1 : h < 1)
    (hs0 : (1 + h) / 2 ≤ s) (hs1 : s < 1) (v : ℝ) :
    rawKernel h 0 (s - v) v =
      (Ioo 0 (h * (1 - s) / (1 - h))).indicator
        (fun v => (h * (1 - s + v))⁻¹) v := by
  have hp : 0 < 1 + h := by linarith
  have hn : 0 < 1 - h := by linarith
  have hR : h * (1 - s) / (1 - h) ≤ s - 1 / 2 := by
    rw [div_le_iff₀ hn]
    nlinarith
  have hL : h * s / (1 + h) ≤ s - 1 / 2 := by
    rw [div_le_iff₀ hp]
    nlinarith
  have heqR : v < h * (1 - s + v) ↔ v < h * (1 - s) / (1 - h) := by
    rw [lt_div_iff₀ hn]
    constructor <;> intro hh <;> nlinarith
  have heqL : v < h * (s - v) ↔ v < h * s / (1 + h) := by
    rw [lt_div_iff₀ hp]
    constructor <;> intro hh <;> nlinarith
  by_cases hv : 0 < v
  · by_cases hvb : v ≤ s - 1 / 2
    · have hd : delta (s - v) = 1 - s + v := by
        unfold delta
        rw [min_eq_right (by linarith)]
        ring
      unfold rawKernel
      rw [hd, ite_eq_left (by linarith)]
      simp only [Set.indicator_apply, mem_Ioo, heqR]
    · have hd : delta (s - v) = s - v := by
        unfold delta
        rw [min_eq_left (by linarith)]
      have hvR : ¬v < h * (1 - s) / (1 - h) := by linarith
      have hvL : ¬v < h * (s - v) := by
        rw [heqL]
        linarith
      unfold rawKernel
      rw [hd]
      simp only [Set.indicator_apply, mem_Ioo, hvR, hvL, and_false, ite_false, ite_self]
  · unfold rawKernel
    simp only [Set.indicator_apply, mem_Ioo, hv, false_and, ite_false, ite_self]

theorem integral_uncut_endpoint_right {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : (1 + h) / 2 ≤ s) (hs1 : s < 1) :
    (∫ v in (0 : ℝ)..1, rawKernel h 0 (s - v) v) =
      h⁻¹ * Real.log ((1 - h)⁻¹) := by
  have hn : 0 < 1 - h := by linarith
  have hR0 : 0 < h * (1 - s) / (1 - h) := div_pos (mul_pos hh0 (by linarith)) hn
  have hR1 : h * (1 - s) / (1 - h) < 1 := by
    rw [div_lt_iff₀ hn]
    nlinarith
  have hfun : (fun v => rawKernel h 0 (s - v) v) =
      (Ioo 0 (h * (1 - s) / (1 - h))).indicator
        (fun v => (h * (1 - s + v))⁻¹) := by
    funext v
    exact uncut_endpoint_right_formula hh0 hh1 hs0 hs1 v
  rw [hfun, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hR0.le]
    simp_rw [mul_inv]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_left (fun z : ℝ => z⁻¹) (1 - s)]
    simp only [add_zero]
    rw [integral_inv_of_pos (by linarith : 0 < 1 - s)
      (by linarith : 0 < 1 - s + h * (1 - s) / (1 - h))]
    have hratio : (1 - s + h * (1 - s) / (1 - h)) / (1 - s) = (1 - h)⁻¹ := by
      field_simp [ne_of_gt (show 0 < 1 - s by linarith), hn.ne']
      ring
    rw [hratio]
  · intro v hv
    apply Set.indicator_of_notMem
    intro hmem
    exact hv ⟨hmem.1, hmem.2.le.trans hR1.le⟩

theorem averagedDensity_right_formula {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : (1 + h) / 2 ≤ s) :
    ScalarEndpointDensity.averagedDensity h s = h⁻¹ * Real.log ((1 - h)⁻¹) := by
  unfold ScalarEndpointDensity.averagedDensity
  congr 1
  calc
    _ = ∫ t in (0 : ℝ)..h, (1 - t)⁻¹ := by
      apply intervalIntegral.integral_congr_Ioo_of_le hh0.le
      intro t ht
      simp only [ScalarEndpointDensity.slopeDensity,
        ite_eq_right (show ¬s ≤ ScalarEndpointDensity.midpoint t by
          unfold ScalarEndpointDensity.midpoint
          linarith [ht.2])]
    _ = Real.log ((1 - h)⁻¹) := by
      rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t⁻¹) 1]
      simp only [sub_zero]
      rw [integral_inv_of_pos (by linarith : 0 < 1 - h) (by norm_num : (0 : ℝ) < 1)]
      simp only [one_div]

theorem integral_uncut_circleEndpoint_right {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : (1 + h) / 2 ≤ s) (hs1 : s < 1) :
    (∫ v in (0 : ℝ)..1, circleKernel h 0 (s - v) v) =
      ScalarEndpointDensity.averagedDensity h s := by
  rw [averagedDensity_right_formula hh0 hh1 hs0]
  calc
    _ = ∫ v in (0 : ℝ)..1, rawKernel h 0 (s - v) v := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro v hv
      exact uncut_endpoint_no_wrap hh0.le hh1.le (by linarith) hs1 hv.1 hv.2
    _ = _ := integral_uncut_endpoint_right hh0 hh1 hs0 hs1

theorem uncut_endpoint_middle_formula {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : 1 / 2 < s) (hs1 : s < (1 + h) / 2) (v : ℝ) :
    rawKernel h 0 (s - v) v =
      (Ioc 0 (s - 1 / 2)).indicator (fun v => (h * (1 - s + v))⁻¹) v +
      (Ioo (s - 1 / 2) (h * s / (1 + h))).indicator
        (fun v => (h * (s - v))⁻¹) v := by
  have hp : 0 < 1 + h := by linarith
  have hn : 0 < 1 - h := by linarith
  have hsunit : s < 1 := by linarith
  have hR : s - 1 / 2 < h * (1 - s) / (1 - h) := by
    rw [lt_div_iff₀ hn]
    nlinarith
  have heqR : v < h * (1 - s + v) ↔ v < h * (1 - s) / (1 - h) := by
    rw [lt_div_iff₀ hn]
    constructor <;> intro hh <;> nlinarith
  have heqL : v < h * (s - v) ↔ v < h * s / (1 + h) := by
    rw [lt_div_iff₀ hp]
    constructor <;> intro hh <;> nlinarith
  by_cases hv : 0 < v
  · by_cases hvb : v ≤ s - 1 / 2
    · have hd : delta (s - v) = 1 - s + v := by
        unfold delta
        rw [min_eq_right (by linarith)]
        ring
      have hvR : v < h * (1 - s + v) := heqR.mpr (lt_of_le_of_lt hvb hR)
      have hvnot : ¬ s - 1 / 2 < v := not_lt_of_ge hvb
      unfold rawKernel
      rw [hd, ite_eq_left (by linarith)]
      simp only [Set.indicator_apply, mem_Ioc, mem_Ioo, hv, hvb, hvR, hvnot,
        and_self, false_and, ite_true, ite_false, add_zero]
    · have hvb' : s - 1 / 2 < v := lt_of_not_ge hvb
      have hd : delta (s - v) = s - v := by
        unfold delta
        rw [min_eq_left (by linarith)]
      unfold rawKernel
      rw [hd]
      by_cases hvL : v < h * s / (1 + h)
      · have hvs : v < s := by
          have := heqL.mpr hvL
          nlinarith
        simp only [ite_eq_left (show 0 ≤ s - v by linarith), Set.indicator_apply,
          mem_Ioc, mem_Ioo, hv, hvb, hvb', hvL, heqL.mpr hvL,
          and_self, and_false, ite_true, ite_false, zero_add]
      · have hvnot : ¬v < h * (s - v) := fun hh => hvL (heqL.mp hh)
        simp only [Set.indicator_apply, mem_Ioc, mem_Ioo, hv, hvb, hvL, hvnot,
          and_false, ite_false, ite_self, add_zero]
  · have hvb : ¬s - 1 / 2 < v := by linarith
    unfold rawKernel
    simp only [Set.indicator_apply, mem_Ioc, mem_Ioo, hv, hvb,
      false_and, ite_false, ite_self, add_zero]

theorem integral_uncut_endpoint_middle {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : 1 / 2 < s) (hs1 : s < (1 + h) / 2) :
    (∫ v in (0 : ℝ)..1, rawKernel h 0 (s - v) v) =
      h⁻¹ * Real.log ((1 + h) / (4 * s * (1 - s))) := by
  have hp : 0 < 1 + h := by linarith
  have hspos : 0 < s := by linarith
  have hsunit : s < 1 := by linarith
  have hB0 : 0 < s - 1 / 2 := by linarith
  have hL : s - 1 / 2 < h * s / (1 + h) := by
    rw [lt_div_iff₀ hp]
    nlinarith
  have hLs : h * s / (1 + h) < s := by
    rw [div_lt_iff₀ hp]
    nlinarith
  have hB1 : s - 1 / 2 < 1 := by linarith
  have hL1 : h * s / (1 + h) < 1 := by linarith
  let fR : ℝ → ℝ := (Ioc 0 (s - 1 / 2)).indicator (fun v => (h * (1 - s + v))⁻¹)
  let fL : ℝ → ℝ := (Ioo (s - 1 / 2) (h * s / (1 + h))).indicator
    (fun v => (h * (s - v))⁻¹)
  have hfR : Integrable fR := by
    apply IntegrableOn.integrable_indicator _ measurableSet_Ioc
    apply IntegrableOn.mono_set _ Ioc_subset_Icc_self
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.inv₀ (by fun_prop)
    intro v hv
    exact ne_of_gt (mul_pos hh0 (by linarith [hv.1]))
  have hfL : Integrable fL := by
    apply IntegrableOn.integrable_indicator _ measurableSet_Ioo
    apply IntegrableOn.mono_set _ Ioo_subset_Icc_self
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.inv₀ (by fun_prop)
    intro v hv
    exact ne_of_gt (mul_pos hh0 (by linarith [hv.2]))
  have hfun : (fun v => rawKernel h 0 (s - v) v) = fun v => fR v + fL v := by
    funext v
    exact uncut_endpoint_middle_formula hh0 hh1 hs0 hs1 v
  have hRint : (∫ v, fR v) = h⁻¹ * Real.log ((1 / 2) / (1 - s)) := by
    dsimp only [fR]
    rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hB0.le]
    simp_rw [mul_inv]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_left (fun z : ℝ => z⁻¹) (1 - s)]
    have hb : 1 - s + (s - 1 / 2) = (1 / 2 : ℝ) := by ring
    rw [hb]
    simp only [add_zero]
    rw [integral_inv_of_pos (by linarith : 0 < 1 - s) (by norm_num : (0 : ℝ) < 1 / 2)]
  have hLint : (∫ v, fL v) = h⁻¹ * Real.log ((1 / 2) / (s - h * s / (1 + h))) := by
    dsimp only [fL]
    rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hL.le]
    simp_rw [mul_inv]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left (fun z : ℝ => z⁻¹) s]
    have hb : s - (s - 1 / 2) = (1 / 2 : ℝ) := by ring
    rw [hb, integral_inv_of_pos (by linarith : 0 < s - h * s / (1 + h))
      (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [hfun, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [integral_add hfR hfL, hRint, hLint, ← mul_add,
      ← Real.log_mul (by positivity) (by positivity)]
    congr 2
    field_simp [ne_of_gt (show 0 < 1 - s by linarith), hspos.ne', hp.ne']
    ring
  · intro v hv
    have hnotR : v ∉ Ioc 0 (s - 1 / 2) :=
      fun ht => hv ⟨ht.1, ht.2.trans hB1.le⟩
    have hnotL : v ∉ Ioo (s - 1 / 2) (h * s / (1 + h)) :=
      fun ht => hv ⟨lt_trans hB0 ht.1, ht.2.le.trans hL1.le⟩
    simp only [fR, fL, Set.indicator_of_notMem hnotR, Set.indicator_of_notMem hnotL, add_zero]

theorem averagedDensity_middle_formula {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : 1 / 2 < s) (hs1 : s < (1 + h) / 2) :
    ScalarEndpointDensity.averagedDensity h s =
      h⁻¹ * Real.log ((1 + h) / (4 * s * (1 - s))) := by
  have hp : 0 < 1 + h := by linarith
  have hspos : 0 < s := by linarith
  have hsunit : s < 1 := by linarith
  have hC0 : 0 < 2 * s - 1 := by linarith
  have hCh : 2 * s - 1 < h := by linarith
  have hC1 : 2 * s - 1 < 1 := by linarith
  have hd := ScalarEndpointDensity.slopeDensity_parameter_integrable hh0.le hh1 s
  have hdl : IntervalIntegrable (fun t => ScalarEndpointDensity.slopeDensity t s)
      volume 0 (2 * s - 1) := hd.mono_set (by
    rw [uIcc_of_le hC0.le, uIcc_of_le hh0.le]
    exact Icc_subset_Icc le_rfl hCh.le)
  have hdr : IntervalIntegrable (fun t => ScalarEndpointDensity.slopeDensity t s)
      volume (2 * s - 1) h := hd.mono_set (by
    rw [uIcc_of_le hCh.le, uIcc_of_le hh0.le]
    exact Icc_subset_Icc hC0.le le_rfl)
  have hleft : (∫ t in (0 : ℝ)..(2 * s - 1), ScalarEndpointDensity.slopeDensity t s) =
      Real.log (1 / (1 - (2 * s - 1))) := by
    calc
      _ = ∫ t in (0 : ℝ)..(2 * s - 1), (1 - t)⁻¹ := by
        apply intervalIntegral.integral_congr_Ioo_of_le hC0.le
        intro t ht
        simp only [ScalarEndpointDensity.slopeDensity,
          ite_eq_right (show ¬s ≤ ScalarEndpointDensity.midpoint t by
            unfold ScalarEndpointDensity.midpoint
            linarith [ht.2])]
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t⁻¹) 1]
        simp only [sub_zero]
        rw [integral_inv_of_pos (by linarith : 0 < 1 - (2 * s - 1))
          (by norm_num : (0 : ℝ) < 1)]
  have hright : (∫ t in (2 * s - 1)..h, ScalarEndpointDensity.slopeDensity t s) =
      Real.log ((1 + h) / (1 + (2 * s - 1))) := by
    calc
      _ = ∫ t in (2 * s - 1)..h, (1 + t)⁻¹ := by
        apply intervalIntegral.integral_congr_Ioo_of_le hCh.le
        intro t ht
        simp only [ScalarEndpointDensity.slopeDensity,
          ite_eq_left (show s ≤ ScalarEndpointDensity.midpoint t by
            unfold ScalarEndpointDensity.midpoint
            linarith [ht.1])]
      _ = _ := by
        rw [intervalIntegral.integral_comp_add_left (fun t : ℝ => t⁻¹) 1]
        rw [integral_inv_of_pos (by linarith : 0 < 1 + (2 * s - 1)) hp]
  unfold ScalarEndpointDensity.averagedDensity
  rw [← intervalIntegral.integral_add_adjacent_intervals hdl hdr, hleft, hright,
    ← Real.log_mul (by positivity) (by positivity)]
  congr 2
  field_simp [hspos.ne', ne_of_gt (show 0 < 1 - s by linarith),
    ne_of_gt (show 0 < 1 - (2 * s - 1) by linarith),
    ne_of_gt (show 0 < 1 + (2 * s - 1) by linarith),
    show (2 : ℝ) - s * 2 ≠ 0 by linarith]
  ring

theorem integral_uncut_circleEndpoint_middle {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : 1 / 2 < s) (hs1 : s < (1 + h) / 2) :
    (∫ v in (0 : ℝ)..1, circleKernel h 0 (s - v) v) =
      ScalarEndpointDensity.averagedDensity h s := by
  rw [averagedDensity_middle_formula hh0 hh1 hs0 hs1]
  calc
    _ = ∫ v in (0 : ℝ)..1, rawKernel h 0 (s - v) v := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro v hv
      exact uncut_endpoint_no_wrap hh0.le hh1.le (by linarith) (by linarith) hv.1 hv.2
    _ = _ := integral_uncut_endpoint_middle hh0 hh1 hs0 hs1

theorem integral_uncut_circleEndpoint {h s : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hs0 : 0 < s) (hs1 : s < 1) :
    (∫ v in (0 : ℝ)..1, circleKernel h 0 (s - v) v) =
      ScalarEndpointDensity.averagedDensity h s := by
  by_cases hleft : s ≤ 1 / 2
  · exact integral_uncut_circleEndpoint_left hh0 hh1.le hs0 hleft
  · by_cases hright : (1 + h) / 2 ≤ s
    · exact integral_uncut_circleEndpoint_right hh0 hh1 hright hs1
    · exact integral_uncut_circleEndpoint_middle hh0 hh1 (lt_of_not_ge hleft) (lt_of_not_ge hright)

end Invariant233.ScalarSampling

end OAI
