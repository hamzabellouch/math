import Mathlib

namespace OAI

namespace AngularTaylor

theorem inv_sqrt_remainder {x : ℝ} (hx : 0 ≤ x) :
    |1 / Real.sqrt (1 + x) - (1 - x / 2)| ≤ (3 / 8) * x ^ 2 := by
  let t := Real.sqrt (1 + x)
  have ht : 1 ≤ t := by
    dsimp [t]
    exact (Real.le_sqrt (by norm_num) (by linarith)).2 (by linarith)
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have ht2 : t ^ 2 = 1 + x := Real.sq_sqrt (by linarith)
  have hden : 0 < 2 * t * (t + 1) ^ 2 := by positivity
  have hfac : 0 ≤ (t + 2) / (2 * t * (t + 1) ^ 2) := by positivity
  have hfac1 : (t + 2) / (2 * t * (t + 1) ^ 2) ≤ 3 / 8 := by
    apply (div_le_iff₀ hden).2
    have hp : 0 ≤ (t - 1) * (3 * t ^ 2 + 9 * t + 8) :=
      mul_nonneg (sub_nonneg.mpr ht) (by positivity)
    nlinarith only [hp]
  have heq : 1 / t - (1 - x / 2) =
      x ^ 2 * ((t + 2) / (2 * t * (t + 1) ^ 2)) := by
    have hxid : x = t ^ 2 - 1 := by linarith only [ht2]
    rw [hxid]
    field_simp
    ring
  change |1 / t - (1 - x / 2)| ≤ (3 / 8) * x ^ 2
  rw [heq, abs_of_nonneg (mul_nonneg (sq_nonneg x) hfac)]
  nlinarith only [mul_le_mul_of_nonneg_left hfac1 (sq_nonneg x)]

theorem bounded_product_remainder {z M A : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hM0 : 0 ≤ M) (hM1 : M ≤ 1 / 4)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) :
    |(1 / 2 + z * M) ^ 2 / Real.sqrt (1 + z * A) -
      (1 / 4 + z * (M - A / 8))| ≤ (47 / 128) * z ^ 2 := by
  let B : ℝ := (1 / 2 + z * M) ^ 2
  let R : ℝ := 1 / Real.sqrt (1 + z * A) - (1 - z * A / 2)
  have hzM0 : 0 ≤ z * M := mul_nonneg hz0 hM0
  have hzM1 : z * M ≤ 1 / 4 := by
    nlinarith only [mul_le_mul hz1 hM1 hM0 (by norm_num : (0 : ℝ) ≤ 1)]
  have hB0 : 0 ≤ B := sq_nonneg _
  have hB1 : B ≤ 9 / 16 := by dsimp [B]; nlinarith only [hzM0, hzM1]
  have hA2 : A ^ 2 ≤ 1 := by nlinarith only [hA0, hA1]
  have hR : |R| ≤ (3 / 8) * z ^ 2 := by
    have h := inv_sqrt_remainder (mul_nonneg hz0 hA0)
    have hb := mul_le_of_le_one_right (sq_nonneg z) hA2
    dsimp [R]
    nlinarith only [h, hb]
  have hBR : |B * R| ≤ (27 / 128) * z ^ 2 := by
    rw [abs_mul, abs_of_nonneg hB0]
    have h := mul_le_mul hB1 hR (abs_nonneg R) (by norm_num : (0 : ℝ) ≤ 9 / 16)
    nlinarith only [h]
  have hM2 : M ^ 2 ≤ 1 / 16 := by nlinarith only [hM0, hM1]
  have hMA0 : 0 ≤ M * A := mul_nonneg hM0 hA0
  have hMA1 : M * A ≤ 1 / 4 := by
    nlinarith only [mul_le_mul hM1 hA1 hA0 (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  have hZM0 : 0 ≤ z * M ^ 2 * A := by positivity
  have hZM1 : z * M ^ 2 * A ≤ 1 / 16 := by
    calc
      z * M ^ 2 * A ≤ 1 * (1 / 16) * 1 := mul_le_mul
        (mul_le_mul hz1 hM2 (sq_nonneg _) (by norm_num)) hA1 hA0 (by norm_num)
      _ = 1 / 16 := by ring
  have hG : |M ^ 2 - M * A / 2 - z * M ^ 2 * A / 2| ≤ 5 / 32 := by
    rw [abs_le]
    constructor <;> nlinarith only [hM2, sq_nonneg M, hMA0, hMA1, hZM0, hZM1]
  have hZG : |z ^ 2 * (M ^ 2 - M * A / 2 - z * M ^ 2 * A / 2)| ≤
      z ^ 2 * (5 / 32) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left hG (sq_nonneg _)
  have hid : (1 / 2 + z * M) ^ 2 / Real.sqrt (1 + z * A) -
      (1 / 4 + z * (M - A / 8)) =
      B * R + z ^ 2 * (M ^ 2 - M * A / 2 - z * M ^ 2 * A / 2) := by
    dsimp [B, R]
    ring
  rw [hid]
  have hab := abs_add_le (B * R) (z ^ 2 * (M ^ 2 - M * A / 2 - z * M ^ 2 * A / 2))
  nlinarith only [hab, hZG, hBR]

end AngularTaylor

end OAI
