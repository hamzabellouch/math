import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The telescoping unit-fraction expansion of the complement of `1/m`. -/
theorem reciprocal_telescope (j : ℕ) :
    (∑ i ∈ Finset.range j, (1 : ℚ) / (((i + 1) * (i + 2) : ℕ) : ℚ)) =
      1 - 1 / ((j + 1 : ℕ) : ℚ) := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have h1 : (j : ℚ) + 1 ≠ 0 := by positivity
    have h2 : (j : ℚ) + 2 ≠ 0 := by positivity
    field_simp
    ring

/-- Consecutive products grow strictly and have gaps larger than one. -/
theorem consecutive_product_gap {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    a * (a + 1) + 1 < b * (b + 1) := by
  have hstep : a + 1 ≤ b := hab
  have hprod : (a + 1) * (a + 2) ≤ b * (b + 1) :=
    Nat.mul_le_mul hstep (by omega)
  nlinarith

/-- If the reserved marker collides with a telescoping denominator, its successor does not. -/
theorem consecutive_product_succ_ne {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a * (a + 1) + 1 ≠ b * (b + 1) := by
  rcases lt_trichotomy a b with h | rfl | h
  · exact ne_of_lt (consecutive_product_gap ha h)
  · omega
  · have := consecutive_product_gap hb h
    omega

end Problem337

end

end OAI
