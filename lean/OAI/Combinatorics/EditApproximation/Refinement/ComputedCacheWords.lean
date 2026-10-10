import OAI.Combinatorics.EditApproximation.Refinement.PhysicalCachedWords
import OAI.Combinatorics.EditApproximation.Refinement.ComputedEarlierInputBudget

namespace OAI

/-! Explicit multiword cache storage after substituting the computed height. -/

namespace EditApproximation

theorem cacheWordBudget_le_cube (H N F r B : ℕ) (hH : 64 ≤ H)
    (hN : Nat.size N ≤ H) (hF : F ≤ H) (hr : r ≤ H) (hB : B ≤ 13 * H) :
    Nat.size ((32 * F + 1) * N) + 2 * r * B + 3 ≤ H ^ 3 := by
  have hFsize : Nat.size F ≤ H := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hF
  have hm := natural_product_bit_length 32 F
  have ha := natural_sum_bit_length (32 * F) 1
  have hp := natural_product_bit_length (32 * F + 1) N
  have h32 : Nat.size 32 = 6 := by decide
  simp only [h32, Nat.size_one] at hm ha
  have hbits : Nat.size ((32 * F + 1) * N) ≤ 2 * H + 8 := by omega
  have hmul := Nat.mul_le_mul hr hB
  have hsquare : 2 * H + 11 ≤ H ^ 2 := by nlinarith
  have hcube := Nat.mul_le_mul_right (H ^ 2) hH
  have hc : 64 * H ^ 2 ≤ H ^ 3 := by
    simpa only [pow_succ'] using hcube
  nlinarith only [hbits, hmul, hsquare, hc, Nat.zero_le (H ^ 2)]

theorem computed_input_size_le_height (N : ℕ) : Nat.size N ≤ inputHeight N := by
  apply Nat.size_le.mpr
  exact (show N < N + 2 by omega).trans_le (inputHeight_covers_length N)

theorem computed_cacheWordBudget_le_cube (N r B : ℕ) (hH : 64 ≤ inputHeight N)
    (hr : r ≤ inputHeight N) (hB : B ≤ 10 * Nat.size (inputSmallLog N) + 3) :
    Nat.size ((32 * inputSmallLog N + 1) * N) + 2 * r * B + 3 ≤ inputHeight N ^ 3 := by
  apply cacheWordBudget_le_cube _ _ _ _ _ hH (computed_input_size_le_height N)
    (computed_smallLog_le_height N) hr
  have hs : Nat.size (inputSmallLog N) ≤ inputHeight N :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (computed_smallLog_le_height N)
  omega

theorem computed_refinementBase_length (N : ℕ) (ell : List Bool)
    (hell : bitWordValue ell = inputSmallLog N) :
    (refinementBaseWithWork ell).1.length ≤ 10 * Nat.size (inputSmallLog N) + 3 := by
  rw [refinementBaseWithWork_length, hell]
  exact refinement_denominator_base_bits _

end EditApproximation

end OAI
