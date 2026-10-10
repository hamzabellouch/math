import OAI.Analysis.KadisonKastler.WordBounds

namespace OAI

/-! # Summing the factorial factors in the preservation cuts -/

namespace KadisonKastler

open Finset

theorem sqrt_factorial_product_eq_div_sqrt_choose (m k : ℕ) (hk : k ≤ m) :
    Real.sqrt (k.factorial : ℝ) * Real.sqrt ((m - k).factorial : ℝ) =
      Real.sqrt (m.factorial : ℝ) / Real.sqrt (m.choose k : ℝ) := by
  have hpos : 0 < Real.sqrt (m.choose k : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.choose_pos hk)
  have hnum : (m.choose k : ℝ) * (k.factorial : ℝ) * ((m - k).factorial : ℝ) =
      (m.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have he : Real.sqrt (m.choose k : ℝ) * Real.sqrt (k.factorial : ℝ) *
      Real.sqrt ((m - k).factorial : ℝ) = Real.sqrt (m.factorial : ℝ) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg _), ← Real.sqrt_mul (by positivity), hnum]
  apply (eq_div_iff (ne_of_gt hpos)).mpr
  calc
    _ = Real.sqrt (m.choose k : ℝ) * Real.sqrt (k.factorial : ℝ) *
        Real.sqrt ((m - k).factorial : ℝ) := by ring
    _ = _ := he

theorem sum_sqrt_factorial_products (m : ℕ) :
    (∑ k ∈ range (m + 1), Real.sqrt (k.factorial : ℝ) *
      Real.sqrt ((m - k).factorial : ℝ)) =
      Real.sqrt (m.factorial : ℝ) *
        ∑ k ∈ range (m + 1), 1 / Real.sqrt (m.choose k : ℝ) := by
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  rw [sqrt_factorial_product_eq_div_sqrt_choose m k (by have := mem_range.mp hk; omega)]
  ring

theorem sum_sqrt_factorial_products_le_five (m : ℕ) :
    (∑ k ∈ range (m + 1), Real.sqrt (k.factorial : ℝ) *
      Real.sqrt ((m - k).factorial : ℝ)) ≤ 5 * Real.sqrt (m.factorial : ℝ) := by
  rw [sum_sqrt_factorial_products]
  exact (mul_le_mul_of_nonneg_left (sum_inv_sqrt_choose_le_five m) (Real.sqrt_nonneg _)).trans_eq
    (mul_comm _ _)

end KadisonKastler

end OAI
