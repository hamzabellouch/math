import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

noncomputable section

namespace InternalCatalan

theorem mixed_denominator_rpow_bound {t s : ℝ}
    (ht : |t| < 1) (hs0 : 0 < s) (hs1 : s < 1) :
    (1 - t * s)⁻¹ ≤
      (1 - |t|) ^ (-(1 / 4) : ℝ) * (1 - s) ^ (-(3 / 4) : ℝ) := by
  have hts_abs : t * s ≤ |t| := calc
    t * s ≤ |t| * s := mul_le_mul_of_nonneg_right (le_abs_self t) hs0.le
    _ ≤ |t| := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hs1.le (abs_nonneg t)
  have hts_s : t * s ≤ s := calc
    t * s ≤ 1 * s :=
      mul_le_mul_of_nonneg_right ((le_abs_self t).trans ht.le) hs0.le
    _ = s := one_mul s
  have ha : 0 < 1 - |t| := sub_pos.mpr ht
  have hb : 0 < 1 - s := sub_pos.mpr hs1
  have hDa : 1 - |t| ≤ 1 - t * s := sub_le_sub_left hts_abs 1
  have hDb : 1 - s ≤ 1 - t * s := sub_le_sub_left hts_s 1
  have hD : 0 < 1 - t * s := ha.trans_le hDa
  calc
    (1 - t * s)⁻¹ =
        (1 - t * s) ^ (-(1 / 4) : ℝ) *
          (1 - t * s) ^ (-(3 / 4) : ℝ) := by
      rw [← Real.rpow_add hD,
        show -(1 / 4 : ℝ) + -(3 / 4 : ℝ) = (-1 : ℝ) by norm_num,
        Real.rpow_neg_one]
    _ ≤ (1 - |t|) ^ (-(1 / 4) : ℝ) * (1 - s) ^ (-(3 / 4) : ℝ) :=
      mul_le_mul
        (Real.rpow_le_rpow_of_nonpos ha hDa (by norm_num))
        (Real.rpow_le_rpow_of_nonpos hb hDb (by norm_num))
        (Real.rpow_nonneg hD.le _) (Real.rpow_nonneg ha.le _)

theorem scalar_weight_le_rpow {t : ℝ} (ht : |t| < 1) :
    |t| / Real.sqrt (1 - t ^ 2) ≤ (1 - |t|) ^ (-(1 / 2) : ℝ) := by
  have ht_sq : t ^ 2 ≤ |t| := by
    have hmul := mul_le_mul_of_nonneg_left ht.le (abs_nonneg t)
    nlinarith [sq_abs t]
  have ha : 0 < 1 - |t| := sub_pos.mpr ht
  have haq : 1 - |t| ≤ 1 - t ^ 2 := sub_le_sub_left ht_sq 1
  have hq : 0 < 1 - t ^ 2 := ha.trans_le haq
  calc
    |t| / Real.sqrt (1 - t ^ 2) ≤ 1 / Real.sqrt (1 - t ^ 2) :=
      div_le_div_of_nonneg_right ht.le (Real.sqrt_nonneg _)
    _ = (1 - t ^ 2) ^ (-(1 / 2) : ℝ) := by
      rw [one_div, Real.sqrt_eq_rpow, Real.rpow_neg hq.le]
    _ ≤ (1 - |t|) ^ (-(1 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos ha haq (by norm_num)

theorem mixed_kernel_norm_le {t s : ℝ} (i j : ℕ)
    (ht : |t| < 1) (hs0 : 0 < s) (hs1 : s < 1) :
    ‖(|t| / Real.sqrt (1 - t ^ 2)) * (t ^ i * s ^ j) / (1 - t * s)‖ ≤
      (1 - |t|) ^ (-(3 / 4) : ℝ) * (1 - s) ^ (-(3 / 4) : ℝ) := by
  have ha : 0 < 1 - |t| := sub_pos.mpr ht
  have hts : t * s < 1 := calc
    t * s ≤ |t| * s := mul_le_mul_of_nonneg_right (le_abs_self t) hs0.le
    _ ≤ |t| := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hs1.le (abs_nonneg t)
    _ < 1 := ht
  have hD : 0 < 1 - t * s := sub_pos.mpr hts
  have hw : 0 ≤ |t| / Real.sqrt (1 - t ^ 2) :=
    div_nonneg (abs_nonneg t) (Real.sqrt_nonneg _)
  have hti : |t| ^ i ≤ 1 := pow_le_one₀ (abs_nonneg t) ht.le
  have hsj : s ^ j ≤ 1 := pow_le_one₀ hs0.le hs1.le
  have hm : |t| ^ i * s ^ j ≤ 1 := by
    have h := mul_le_mul hti hsj (pow_nonneg hs0.le j) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using h
  calc
    ‖(|t| / Real.sqrt (1 - t ^ 2)) * (t ^ i * s ^ j) / (1 - t * s)‖ =
        ((|t| / Real.sqrt (1 - t ^ 2)) * (|t| ^ i * s ^ j)) *
          (1 - t * s)⁻¹ := by
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hw,
        abs_mul, abs_pow, abs_pow, abs_of_nonneg hs0.le, abs_of_pos hD,
        div_eq_mul_inv]
    _ ≤ ((|t| / Real.sqrt (1 - t ^ 2)) * 1) * (1 - t * s)⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hw)
        (inv_nonneg.mpr hD.le)
    _ = (|t| / Real.sqrt (1 - t ^ 2)) * (1 - t * s)⁻¹ := by rw [mul_one]
    _ ≤ (1 - |t|) ^ (-(1 / 2) : ℝ) *
        ((1 - |t|) ^ (-(1 / 4) : ℝ) * (1 - s) ^ (-(3 / 4) : ℝ)) :=
      mul_le_mul (scalar_weight_le_rpow ht) (mixed_denominator_rpow_bound ht hs0 hs1)
        (inv_nonneg.mpr hD.le) (Real.rpow_nonneg ha.le _)
    _ = (1 - |t|) ^ (-(3 / 4) : ℝ) * (1 - s) ^ (-(3 / 4) : ℝ) := by
      rw [← mul_assoc, ← Real.rpow_add ha,
        show -(1 / 2 : ℝ) + -(1 / 4 : ℝ) = -(3 / 4 : ℝ) by norm_num]

theorem norm_mixedKernel_le (i j : ℕ) {t s : ℝ}
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1) (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    ‖(|t| / Real.sqrt (1 - t ^ 2)) * (t ^ i * s ^ j) / (1 - t * s)‖ ≤
      (1 - |t|) ^ (-(3 / 4) : ℝ) * (1 - s) ^ (-(3 / 4) : ℝ) :=
  mixed_kernel_norm_le i j (abs_lt.mpr ht) hs.1 hs.2

end InternalCatalan

end

end OAI
