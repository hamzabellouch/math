import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic

namespace OAI

namespace Invariant233.ModuloIntervalMeasure

open Set MeasureTheory
open scoped ENNReal

theorem integral_periodic_le_length_add_one {f : ℝ → ℝ}
    (hperiod : Function.Periodic f 1) (hf : ∀ x, 0 ≤ f x)
    (hint : IntervalIntegrable f volume 0 1) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, f x) ≤ (b - a + 1) * ∫ x in (0 : ℝ)..1, f x := by
  let n : ℕ := ⌈b - a⌉₊
  have hn : b ≤ a + n := by
    have := Nat.le_ceil (b - a)
    dsimp [n]
    linarith
  have hn' : (n : ℝ) ≤ b - a + 1 := by
    exact (Nat.ceil_lt_add_one (sub_nonneg.mpr hab)).le
  have hint' := hperiod.intervalIntegrable₀ (by norm_num : (1 : ℝ) ≠ 0) hint
  have hmass : 0 ≤ ∫ x in (0 : ℝ)..1, f x :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) hf
  calc
    (∫ x in a..b, f x) ≤ ∫ x in a..a + n, f x :=
      intervalIntegral.integral_mono_interval le_rfl hab hn
        (Filter.Eventually.of_forall hf) (hint' _ _)
    _ = (n : ℝ) * ∫ x in (0 : ℝ)..1, f x := by
      have h := hperiod.intervalIntegral_add_zsmul_eq (n : ℤ) a hint'
      simpa only [zsmul_eq_mul, Int.cast_natCast, mul_one,
        hperiod.intervalIntegral_add_eq a 0, zero_add] using h
    _ ≤ (b - a + 1) * ∫ x in (0 : ℝ)..1, f x :=
      mul_le_mul_of_nonneg_right hn' hmass

theorem periodic_fract_indicator (s : Set ℝ) :
    Function.Periodic ((Int.fract ⁻¹' s).indicator (fun _ => (1 : ℝ))) 1 := by
  classical
  intro x
  change (if Int.fract (x + 1) ∈ s then (1 : ℝ) else 0) =
    (if Int.fract x ∈ s then 1 else 0)
  rw [Int.fract_add_one]

theorem intervalIntegrable_indicator_one {s : Set ℝ} (hs : MeasurableSet s)
    (a b : ℝ) : IntervalIntegrable (s.indicator (fun _ => (1 : ℝ))) volume a b := by
  exact ⟨(integrable_const (1 : ℝ)).indicator hs,
    (integrable_const (1 : ℝ)).indicator hs⟩

theorem integral_fract_indicator_one_period {s : Set ℝ} (hs : MeasurableSet s) :
    (∫ x in (0 : ℝ)..1, (Int.fract ⁻¹' s).indicator (fun _ => (1 : ℝ)) x) =
      volume.real (s ∩ Ico 0 1) := by
  calc
    (∫ x in (0 : ℝ)..1, (Int.fract ⁻¹' s).indicator (fun _ => (1 : ℝ)) x) =
        ∫ x in (0 : ℝ)..1, s.indicator (fun _ => (1 : ℝ)) x := by
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      classical
      intro x hx
      have hfract := Int.fract_eq_self.mpr ⟨hx.1.le, hx.2⟩
      change (if Int.fract x ∈ s then (1 : ℝ) else 0) =
        (if x ∈ s then 1 else 0)
      rw [hfract]
    _ = volume.real (s ∩ Ico 0 1) := by
      rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Ico_eq_integral_Ioc,
        integral_indicator_const 1 hs, measureReal_restrict_apply hs]
      simp

theorem volume_fract_preimage_inter_Ioc_le {s : Set ℝ} (hs : MeasurableSet s)
    {a b : ℝ} (hab : a ≤ b) :
    volume.real (Int.fract ⁻¹' s ∩ Ioc a b) ≤
      (b - a + 1) * volume.real (s ∩ Ico 0 1) := by
  have hs' : MeasurableSet (Int.fract ⁻¹' s) := hs.preimage measurable_fract
  have hnonneg : ∀ x, 0 ≤ (Int.fract ⁻¹' s).indicator (fun _ => (1 : ℝ)) x := by
    intro x
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have h := integral_periodic_le_length_add_one (periodic_fract_indicator s) hnonneg
    (intervalIntegrable_indicator_one hs' 0 1) hab
  rw [integral_fract_indicator_one_period hs, intervalIntegral.integral_of_le hab,
    integral_indicator_const 1 hs', measureReal_restrict_apply hs'] at h
  simpa only [smul_eq_mul, mul_one] using h

theorem cond_fract_preimage_le {s : Set ℝ} (hs : MeasurableSet s)
    {a b : ℝ} (hab : a < b) :
    (ProbabilityTheory.cond volume (Ioc a b)).real (Int.fract ⁻¹' s) ≤
      (1 + 1 / (b - a)) * volume.real (s ∩ Ico 0 1) := by
  have hr : 0 < b - a := sub_pos.mpr hab
  have h := mul_le_mul_of_nonneg_left
    (volume_fract_preimage_inter_Ioc_le hs hab.le) (inv_nonneg.mpr hr.le)
  rw [ProbabilityTheory.cond, measureReal_ennreal_smul_apply,
    measureReal_restrict_apply (hs.preimage measurable_fract),
    ENNReal.toReal_inv, Real.volume_Ioc, ENNReal.toReal_ofReal hr.le]
  calc
    _ ≤ (b - a)⁻¹ * ((b - a + 1) * volume.real (s ∩ Ico 0 1)) := h
    _ = (1 + 1 / (b - a)) * volume.real (s ∩ Ico 0 1) := by
      rw [← mul_assoc, mul_add, inv_mul_cancel₀ hr.ne', mul_one, one_div]

theorem threshold_miss_unit_volume_le {w : ℝ} (hw : 0 ≤ w) :
    volume.real ({u : ℝ | 1 - u ∉ Icc w (1 - w)} ∩ Ico 0 1) ≤ 2 * w := by
  have hsub : {u : ℝ | 1 - u ∉ Icc w (1 - w)} ∩ Ico 0 1 ⊆
      Ico 0 w ∪ Ioo (1 - w) 1 := by
    intro u hu
    rcases hu with ⟨hbad, hu0, hu1⟩
    by_cases huw : u < w
    · exact Or.inl ⟨hu0, huw⟩
    · right
      refine ⟨?_, hu1⟩
      by_contra h
      apply hbad
      constructor <;> linarith
  calc
    volume.real ({u : ℝ | 1 - u ∉ Icc w (1 - w)} ∩ Ico 0 1) ≤
        volume.real (Ico 0 w ∪ Ioo (1 - w) 1) := measureReal_mono hsub (measure_union_lt_top
          (by rw [Real.volume_Ico]; exact ENNReal.ofReal_lt_top)
          (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)).ne
    _ ≤ volume.real (Ico 0 w) + volume.real (Ioo (1 - w) 1) :=
      measureReal_union_le _ _
    _ = 2 * w := by
      rw [Real.volume_real_Ico_of_le hw, Real.volume_real_Ioo_of_le (by linarith)]
      ring

theorem cond_threshold_miss_le {a b w : ℝ} (hlen : (1 : ℝ) / 4 ≤ b - a)
    (hw : 0 ≤ w) :
    (ProbabilityTheory.cond volume (Ioc a b)).real
      {t : ℝ | 1 - Int.fract t ∉ Icc w (1 - w)} ≤ 10 * w := by
  have hab : a < b := by linarith
  have hs : MeasurableSet {u : ℝ | 1 - u ∉ Icc w (1 - w)} :=
    (measurableSet_Icc.preimage (measurable_const.sub measurable_id)).compl
  have h := cond_fract_preimage_le hs hab
  have hr : 0 < b - a := sub_pos.mpr hab
  have hfactor : 1 + 1 / (b - a) ≤ 5 := by
    have : 1 / (b - a) ≤ 4 := (div_le_iff₀ hr).mpr (by linarith)
    linarith
  change (ProbabilityTheory.cond volume (Ioc a b)).real (Int.fract ⁻¹'
    {u : ℝ | 1 - u ∉ Icc w (1 - w)}) ≤ 10 * w
  calc
    _ ≤ (1 + 1 / (b - a)) * volume.real
        ({u : ℝ | 1 - u ∉ Icc w (1 - w)} ∩ Ico 0 1) := h
    _ ≤ 5 * (2 * w) := mul_le_mul hfactor (threshold_miss_unit_volume_le hw)
      measureReal_nonneg (by norm_num)
    _ = 10 * w := by ring

theorem cond_Icc_eq_cond_Ioc (a b : ℝ) :
    ProbabilityTheory.cond volume (Icc a b) = ProbabilityTheory.cond volume (Ioc a b) := by
  simp only [ProbabilityTheory.cond, Real.volume_Icc, Real.volume_Ioc]
  rw [Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume)).symm]

theorem cond_uIcc_mul_preimage (a b k : ℝ) (hk : k ≠ 0) (s : Set ℝ) :
    (ProbabilityTheory.cond volume (uIcc a b)).real ((k * ·) ⁻¹' s) =
      (ProbabilityTheory.cond volume (uIcc (k * a) (k * b))).real s := by
  have hpre : (k * ·) ⁻¹' uIcc (k * a) (k * b) = uIcc a b := by
    rw [preimage_const_mul_uIcc hk]
    field_simp
  have hbase : volume (uIcc a b) =
      ENNReal.ofReal |k⁻¹| * volume (uIcc (k * a) (k * b)) := by
    rw [← hpre, Real.volume_preimage_mul_left hk]
  have hinter : volume (uIcc a b ∩ (k * ·) ⁻¹' s) =
      ENNReal.ofReal |k⁻¹| * volume (uIcc (k * a) (k * b) ∩ s) := by
    rw [← hpre, ← preimage_inter, Real.volume_preimage_mul_left hk]
  simp only [measureReal_def, ProbabilityTheory.cond_apply measurableSet_uIcc,
    hbase, hinter, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (abs_nonneg k⁻¹), mul_inv_rev]
  have hscale : |k⁻¹| ≠ 0 := abs_ne_zero.mpr (inv_ne_zero hk)
  rw [mul_assoc, ← mul_assoc |k⁻¹|⁻¹, inv_mul_cancel₀ hscale, one_mul]

theorem cond_uIcc_threshold_miss_le {a b w : ℝ}
    (hlen : (1 : ℝ) / 4 ≤ |b - a|) (hw : 0 ≤ w) :
    (ProbabilityTheory.cond volume (uIcc a b)).real
      {t : ℝ | 1 - Int.fract t ∉ Icc w (1 - w)} ≤ 10 * w := by
  rw [uIcc, cond_Icc_eq_cond_Ioc]
  apply cond_threshold_miss_le _ hw
  simpa only [max_sub_min_eq_abs] using hlen

theorem uniform_angle_threshold_miss_le {N k w : ℝ} (hN : 0 < N)
    (hk : N / 4 ≤ |k|) (hw : 0 ≤ w) :
    (ProbabilityTheory.cond volume (Icc (1 / N) (2 / N))).real
      {θ : ℝ | 1 - Int.fract (k * θ) ∉ Icc w (1 - w)} ≤ 10 * w := by
  have hk0 : k ≠ 0 := by
    intro h
    simp only [h, abs_zero] at hk
    linarith
  have hab : (1 : ℝ) / N ≤ 2 / N := by
    apply div_le_div_of_nonneg_right (by norm_num) hN.le
  rw [← uIcc_of_le hab]
  change (ProbabilityTheory.cond volume (uIcc (1 / N) (2 / N))).real
    ((k * ·) ⁻¹' {t : ℝ | 1 - Int.fract t ∉ Icc w (1 - w)}) ≤ 10 * w
  rw [cond_uIcc_mul_preimage _ _ _ hk0]
  apply cond_uIcc_threshold_miss_le _ hw
  have hlength : |k * (2 / N) - k * (1 / N)| = |k| / N := by
    rw [← mul_sub, ← sub_div, show (2 : ℝ) - 1 = 1 by norm_num,
      mul_one_div, abs_div, abs_of_pos hN]
  rw [hlength]
  exact (le_div_iff₀ hN).mpr (by linarith)

theorem uniform_angle_isProbabilityMeasure {N : ℝ} (hN : 0 < N) :
    IsProbabilityMeasure (ProbabilityTheory.cond volume (Icc (1 / N) (2 / N))) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc]
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    exact sub_pos.mpr ((div_lt_div_iff_of_pos_right hN).mpr (by norm_num))
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

theorem uniform_angle_threshold_miss_le_ennreal {N k w : ℝ} (hN : 0 < N)
    (hk : N / 4 ≤ |k|) (hw : 0 ≤ w) :
    (ProbabilityTheory.cond volume (Icc (1 / N) (2 / N)))
      {θ : ℝ | 1 - Int.fract (k * θ) ∉ Icc w (1 - w)} ≤ ENNReal.ofReal (10 * w) := by
  let := uniform_angle_isProbabilityMeasure hN
  have h := ENNReal.ofReal_le_ofReal (uniform_angle_threshold_miss_le hN hk hw)
  rw [ofReal_measureReal (measure_ne_top _ _)] at h
  exact h

end Invariant233.ModuloIntervalMeasure

end OAI
