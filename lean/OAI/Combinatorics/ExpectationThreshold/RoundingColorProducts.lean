import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum

namespace OAI

/-!
# Products controlled by the total color level

The numerical color variable is a quotient of powers. This retains its correct
value when a color level exceeds four, without truncated natural subtraction.
Only the total level over the selected finite set enters the product bound.
-/

namespace TalagrandThreshold

open scoped BigOperators

variable {α : Type*}

/-- Separate the fixed numerator from the sum of all color exponents. -/
theorem colorProduct_eq_pow_div_pow (S : Finset α) (a : α → ℕ) :
    (∏ x ∈ S, (512 : ℝ) ^ 4 / (512 : ℝ) ^ a x) =
      (512 : ℝ) ^ (4 * S.card) / (512 : ℝ) ^ (∑ x ∈ S, a x) := by
  rw [Finset.prod_div_distrib (s := S)
    (fun _ : α => (512 : ℝ) ^ 4) (fun x : α => (512 : ℝ) ^ a x)]
  rw [Finset.prod_const, Finset.prod_pow_eq_pow_sum S a (512 : ℝ), ← pow_mul]

/-- Average color at most four forces the numerical product to be at least one. -/
theorem one_le_colorProduct_of_sum_le (S : Finset α) (a : α → ℕ)
    (hsum : (∑ x ∈ S, a x) ≤ 4 * S.card) :
    1 ≤ ∏ x ∈ S, (512 : ℝ) ^ 4 / (512 : ℝ) ^ a x := by
  rw [colorProduct_eq_pow_div_pow S a]
  apply (one_le_div (pow_pos (by norm_num : (0 : ℝ) < 512) _)).mpr
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 512) hsum

end TalagrandThreshold

end OAI
