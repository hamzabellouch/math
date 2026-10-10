import Mathlib

namespace OAI

namespace CylinderCovering.Analytic

theorem inv_sqrt_remainder_bounds {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ 1 / Real.sqrt (1 + x) - (1 - x / 2) ∧
    1 / Real.sqrt (1 + x) - (1 - x / 2) ≤ 3 / 8 * x ^ 2 := by
  let t := Real.sqrt (1 + x)
  have ht : 1 ≤ t := by
    dsimp [t]
    exact (Real.le_sqrt (by norm_num) (by linarith)).2 (by linarith)
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have ht2 : t ^ 2 = 1 + x := Real.sq_sqrt (by linarith)
  have hden : 0 < 2 * t * (t + 1) ^ 2 := by positivity
  have hfac0 : 0 ≤ (t + 2) / (2 * t * (t + 1) ^ 2) := by positivity
  have hfac : (t + 2) / (2 * t * (t + 1) ^ 2) ≤ 3 / 8 := by
    apply (div_le_iff₀ hden).2
    have hp : 0 ≤ (t - 1) * (6 * t ^ 2 + 18 * t + 16) :=
      mul_nonneg (sub_nonneg.mpr ht) (by positivity)
    nlinarith only [hp]
  have heq : 1 / t - (1 - x / 2) =
      x ^ 2 * ((t + 2) / (2 * t * (t + 1) ^ 2)) := by
    have hxid : x = t ^ 2 - 1 := by linarith only [ht2]
    rw [hxid]
    field_simp
    ring
  change 0 ≤ 1 / t - (1 - x / 2) ∧ _
  rw [heq]
  constructor
  · exact mul_nonneg (sq_nonneg x) hfac0
  · calc
      x ^ 2 * ((t + 2) / (2 * t * (t + 1) ^ 2)) ≤ x ^ 2 * (3 / 8) :=
        mul_le_mul_of_nonneg_left hfac (sq_nonneg x)
      _ = 3 / 8 * x ^ 2 := by ring

theorem inv_sqrt_remainder_abs {x : ℝ} (hx : 0 ≤ x) :
    |1 / Real.sqrt (1 + x) - (1 - x / 2)| ≤ 3 / 8 * x ^ 2 := by
  obtain ⟨h0, h1⟩ := inv_sqrt_remainder_bounds hx
  rwa [abs_of_nonneg h0]

theorem angular_product_remainder {z M A : ℝ}
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hM0 : 0 ≤ M) (hM1 : M ≤ 1 / 4)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) :
    |(1 / 2 + z * M) ^ 2 / Real.sqrt (1 + z * A) -
      (1 / 4 + z * (M - A / 8))| ≤ 55 / 128 * z ^ 2 := by
  let P : ℝ := (1 / 2 + z * M) ^ 2
  let R : ℝ := 1 / Real.sqrt (1 + z * A) - (1 - z * A / 2)
  have hzM0 : 0 ≤ z * M := mul_nonneg hz0 hM0
  have hzM1 : z * M ≤ 1 / 4 := by
    calc
      z * M ≤ 1 * (1 / 4) := mul_le_mul hz1 hM1 hM0 (by norm_num)
      _ = 1 / 4 := by ring
  have hP0 : 0 ≤ P := sq_nonneg _
  have hP1 : P ≤ 9 / 16 := by
    dsimp [P]
    nlinarith only [hzM0, hzM1]
  have hR : |R| ≤ 3 / 8 * z ^ 2 := by
    have h := inv_sqrt_remainder_abs (mul_nonneg hz0 hA0)
    have hA2 : A ^ 2 ≤ 1 := by nlinarith only [hA0, hA1]
    have hb := mul_le_of_le_one_right (sq_nonneg z) hA2
    dsimp [R]
    exact h.trans (by nlinarith only [hb])
  have hPR : |P * R| ≤ 27 / 128 * z ^ 2 := by
    rw [abs_mul, abs_of_nonneg hP0]
    have h := mul_le_mul hP1 hR (abs_nonneg R) (by norm_num : (0 : ℝ) ≤ 9 / 16)
    nlinarith only [h]
  have hM2 : M ^ 2 ≤ 1 / 16 := by nlinarith only [hM0, hM1]
  have hMA0 : 0 ≤ M * A := mul_nonneg hM0 hA0
  have hMA1 : M * A ≤ 1 / 4 := by
    have h := mul_le_mul hM1 hA1 hA0 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    nlinarith only [h]
  have hzMA0 : 0 ≤ z * M ^ 2 * A := by positivity
  have hzMA1 : z * M ^ 2 * A ≤ 1 / 16 := by
    have h := mul_le_mul
      (mul_le_mul hz1 hM2 (sq_nonneg M) (by norm_num : (0 : ℝ) ≤ 1))
      hA1 hA0 (by norm_num : (0 : ℝ) ≤ 1 * (1 / 16))
    nlinarith only [h]
  have hG : |M ^ 2 - M * A / 2 - z * M ^ 2 * A / 2| ≤ 7 / 32 := by
    rw [abs_le]
    constructor <;>
      nlinarith only [hM2, sq_nonneg M, hMA0, hMA1, hzMA0, hzMA1]
  have hzG : |z ^ 2 * (M ^ 2 - M * A / 2 - z * M ^ 2 * A / 2)| ≤
      z ^ 2 * (7 / 32) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg z)]
    exact mul_le_mul_of_nonneg_left hG (sq_nonneg z)
  have hid : (1 / 2 + z * M) ^ 2 / Real.sqrt (1 + z * A) -
      (1 / 4 + z * (M - A / 8)) =
      P * R + z ^ 2 * (M ^ 2 - M * A / 2 - z * M ^ 2 * A / 2) := by
    dsimp [P, R]
    ring
  rw [hid]
  have h := abs_add_le (P * R) (z ^ 2 * (M ^ 2 - M * A / 2 - z * M ^ 2 * A / 2))
  nlinarith only [h, hPR, hzG]

end CylinderCovering.Analytic

end OAI
