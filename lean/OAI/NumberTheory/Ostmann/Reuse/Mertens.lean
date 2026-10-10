import PrimeNumberTheoremAnd.Erdos970.MertensClassical

namespace OAI

open Erdos970

namespace Ostmann.Reuse

theorem primeReciprocal_abs_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |(∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p) -
        Real.log (Real.log x)| ≤ C := by
  obtain ⟨C, hC⟩ := Erdos970.Mertens.sum_prime_div_eq_log_log
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx
  exact (hC x hx).trans (le_max_left _ _)

theorem primeReciprocal_lower_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      Real.log (Real.log x) - C ≤
        ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p := by
  obtain ⟨C, hC, h⟩ := primeReciprocal_abs_error_bound
  refine ⟨C, hC, ?_⟩
  intro x hx
  have := (abs_le.mp (h x hx)).1
  linarith

end Ostmann.Reuse

end OAI
