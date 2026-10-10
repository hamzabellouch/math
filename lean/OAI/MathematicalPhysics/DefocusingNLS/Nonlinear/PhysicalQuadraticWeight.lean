import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingLowInterpolation

namespace OAI

/-! # Two physical derivatives cost two Sobolev orders, uniformly in the radius -/

namespace DefocusingNLS

theorem physical_quadratic_weight (a k x r : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hr : 0 ≤ r) :
    r ^ 4 * ((x + r ^ 2) ^ (6 - a) + r ^ (2 * k)) ≤
      (2 ^ (6 - a) + 1) * ((x + r ^ 2) ^ (6 - a) + r ^ (2 * (k + 2))) := by
  have hA : 0 ≤ (x + r ^ 2) ^ (6 - a) := Real.rpow_nonneg (by positivity) _
  have hP : 0 ≤ r ^ (2 * (k + 2)) := Real.rpow_nonneg hr _
  have hC : 0 ≤ (2 : ℝ) ^ (6 - a) := Real.rpow_nonneg (by norm_num) _
  have hpow : r ^ 4 * r ^ (2 * k) = r ^ (2 * (k + 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add' hr]
    · congr 1
      ring
    · push_cast
      linarith
  by_cases hr1 : r ≤ 1
  · have hr4 : r ^ 4 ≤ 1 := pow_le_one₀ hr hr1
    have ht := mul_le_mul_of_nonneg_right hr4 hA
    rw [mul_add, hpow]
    nlinarith
  · have hrr : 1 ≤ r := (lt_of_not_ge hr1).le
    have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hrr
    have hr2 : 1 ≤ r ^ 2 := one_le_pow₀ hrr
    have hb : (x + r ^ 2) ^ (6 - a) ≤
        (2 : ℝ) ^ (6 - a) * r ^ (2 * (6 - a)) := by
      calc
        _ ≤ (2 * r ^ 2) ^ (6 - a) := Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
        _ = _ := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg r),
            ← Real.rpow_natCast, ← Real.rpow_mul hr]
          norm_num
    have he : r ^ 4 * r ^ (2 * (6 - a)) = r ^ (4 + 2 * (6 - a)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hrp]
      norm_num
    have hp : r ^ (4 + 2 * (6 - a)) ≤ r ^ (2 * (k + 2)) := by
      apply Real.rpow_le_rpow_of_exponent_le hrr
      linarith
    have hbound := mul_le_mul_of_nonneg_left hb (pow_nonneg hr 4)
    have ht := mul_le_mul_of_nonneg_left hp hC
    rw [mul_left_comm, he] at hbound
    rw [mul_add, hpow]
    nlinarith

end DefocusingNLS

end OAI
