import OAI.NumberTheory.TwoPoint.Bounds.SieveGoldbachTruncation
import OAI.NumberTheory.TwoPoint.Bounds.SieveEulerLower

namespace OAI

/-! The dimension-two denominator bound for the finite Goldbach sieve. -/

namespace TwoPointCorrelations

open Finset Problem337
open scoped Classical

lemma sieve_goldbach_denominator_two_scale :
    ∃ c : ℝ, 0 < c ∧ ∀ N z : ℕ, 2 ∣ N → N ≠ 0 → 2 ≤ z →
      ∀ y : ℝ, 2 ≤ y →
      4 * (Real.log y + halaszMertensConstant) ≤ Real.log z →
      c * Real.log y ^ 2 / sieveSingularFactor N ≤
        GoldbachSelberg.denominator N (primorial z) z := by
  obtain ⟨c, hc, hEuler⟩ := sieve_euler_product_log_lower
  refine ⟨c ^ 2 / 2, by positivity, ?_⟩
  intro N z hN hN0 hz y hy hscale
  have hylog : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have he := pow_le_pow_left₀ (mul_nonneg hc.le hylog) (hEuler y hy) 2
  have hprod := sieve_goldbach_product_lower hN hN0 (sievePrimesUpTo y) (sievePrimesUpTo_prime y)
  have hden := sieve_goldbach_denominator_small_primes N z hN hz (by linarith) hscale
  have hS := sieve_singular_factor_pos N
  have hdiv := div_le_div_of_nonneg_right he hS.le
  calc
    _ = (c * Real.log y) ^ 2 / sieveSingularFactor N / 2 := by ring
    _ ≤ (∏ p ∈ sievePrimesUpTo y, sieveEulerFactor p) ^ 2 / sieveSingularFactor N / 2 := by
      linarith
    _ ≤ (∏ p ∈ sievePrimesUpTo y, (1 + sieveGoldbachWeight N p)) / 2 := by linarith
    _ ≤ _ := hden

/-- A single explicit logarithmic lower threshold gives the usual
`log(z)^2 / singularFactor(N)` denominator. -/
theorem sieve_goldbach_denominator_log_square :
    ∃ c : ℝ, 0 < c ∧ ∀ N z : ℕ, 2 ∣ N → N ≠ 0 → 2 ≤ z →
      8 * (halaszMertensConstant + Real.log 2) ≤ Real.log z →
      c * Real.log z ^ 2 / sieveSingularFactor N ≤
        GoldbachSelberg.denominator N (primorial z) z := by
  obtain ⟨c, hc, hden⟩ := sieve_goldbach_denominator_two_scale
  refine ⟨c / 64, by positivity, ?_⟩
  intro N z hN hN0 hz hscale
  let y := Real.exp (Real.log z / 8)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hy : 2 ≤ y := by
    rw [show (2 : ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)]]
    apply Real.exp_le_exp.mpr
    linarith [halaszMertensConstant_nonneg]
  have hylog : Real.log y = Real.log z / 8 := Real.log_exp _
  have ht : 4 * (Real.log y + halaszMertensConstant) ≤ Real.log z := by
    rw [hylog]
    linarith
  have he := hden N z hN hN0 hz y hy ht
  rw [hylog] at he
  convert he using 1
  ring

end TwoPointCorrelations

end OAI
