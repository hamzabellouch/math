import Mathlib

namespace OAI

/-! # A product-power rate is dominated by the two positive factors -/

namespace RegularPointCoordinates

theorem bounded_product_power_rate {a b A B U V da db : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : a ≤ A) (hb : b ≤ B)
    (hU : |da| ≤ U) (hV : |db| ≤ V) (q : ℕ) :
    |(q:ℝ)*(a*b)^(q-1)*(da*b+a*db)| ≤
      ((q:ℝ)*(A*B)^(q-1)*max U V)*(a+b) := by
  have hA : 0 ≤ A := ha0.trans ha
  have hB : 0 ≤ B := hb0.trans hb
  have hU0 : 0 ≤ U := (abs_nonneg _).trans hU
  have hV0 : 0 ≤ V := (abs_nonneg _).trans hV
  have hbase : a*b ≤ A*B := mul_le_mul ha hb hb0 hA
  have hpow := pow_le_pow_left₀ (mul_nonneg ha0 hb0) hbase (q-1)
  have hsum : |da*b+a*db| ≤ max U V*(a+b) := by
    calc
      _ ≤ |da*b|+|a*db| := abs_add_le _ _
      _ = |da| *b+a*|db| := by rw [abs_mul,abs_mul,abs_of_nonneg ha0,abs_of_nonneg hb0]
      _ ≤ U*b+a*V := add_le_add (mul_le_mul_of_nonneg_right hU hb0)
        (mul_le_mul_of_nonneg_left hV ha0)
      _ ≤ max U V*b+a*max U V := add_le_add
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hb0)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) ha0)
      _ = _ := by ring
  rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg q),
    abs_of_nonneg (pow_nonneg (mul_nonneg ha0 hb0) _)]
  calc
    _ ≤ ((q:ℝ)*(A*B)^(q-1))*(max U V*(a+b)) := mul_le_mul
      (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg q)) hsum (abs_nonneg _) (by positivity)
    _ = _ := by ring

end RegularPointCoordinates

end OAI
