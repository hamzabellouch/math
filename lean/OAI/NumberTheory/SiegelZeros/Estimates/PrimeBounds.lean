import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.Chebyshev

namespace OAI


namespace SiegelZeros.W08

open Finset

noncomputable def primesUpTo (x : ℝ) : Finset ℕ :=
  (Ioc 0 ⌊x⌋₊).filter Nat.Prime

noncomputable def primeLogMass (x : ℝ) : ℝ :=
  ∑ p ∈ primesUpTo x, Real.log (p : ℝ) / p

theorem sum_prime_log_eq_theta (x : ℝ) :
    (∑ p ∈ primesUpTo x, Real.log (p : ℝ)) = Chebyshev.theta x := rfl

theorem sum_prime_log_le {x : ℝ} (hx : 0 ≤ x) :
    (∑ p ∈ primesUpTo x, Real.log (p : ℝ)) ≤ Real.log 4 * x :=
  Chebyshev.theta_le_log4_mul_x hx

theorem sum_selected_prime_log_le {x : ℝ} (hx : 0 ≤ x)
    (P : ℕ → Prop) [DecidablePred P] :
    (∑ p ∈ (primesUpTo x).filter P, Real.log (p : ℝ)) ≤ Real.log 4 * x := by
  apply le_trans _ (sum_prime_log_le hx)
  apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
  intro p hp _
  exact Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le)

theorem sum_prime_divisor_mass_le_log {q : ℕ} (hq : q ≠ 0)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ p ∣ q) :
    (∑ p ∈ s, Real.log (p : ℝ) / p) ≤ Real.log (q : ℝ) := by
  calc
    (∑ p ∈ s, Real.log (p : ℝ) / p) ≤
        ∑ p ∈ s, ArithmeticFunction.vonMangoldt p := by
      apply sum_le_sum
      intro p hp
      rw [ArithmeticFunction.vonMangoldt_apply_prime (hs p hp).1]
      exact div_le_self (Real.log_nonneg (by exact_mod_cast (hs p hp).1.one_le))
        (by exact_mod_cast (hs p hp).1.one_le)
    _ ≤ ∑ d ∈ q.divisors, ArithmeticFunction.vonMangoldt d := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact Nat.mem_divisors.mpr ⟨(hs p hp).2, hq⟩
      · intro d _ _
        exact ArithmeticFunction.vonMangoldt_nonneg
    _ = Real.log (q : ℝ) := ArithmeticFunction.vonMangoldt_sum

theorem sum_primeFactors_mass_le_log {q : ℕ} (hq : q ≠ 0) :
    (∑ p ∈ q.primeFactors, Real.log (p : ℝ) / p) ≤ Real.log (q : ℝ) := by
  apply sum_prime_divisor_mass_le_log hq
  intro p hp
  exact ⟨Nat.prime_of_mem_primeFactors hp, Nat.dvd_of_mem_primeFactors hp⟩

theorem replace_chebyshev_error {x M A B : ℝ} (hx : 0 ≤ x) (hM : 0 ≤ M)
    (hfinite : A - M * (∑ p ∈ primesUpTo x, Real.log (p : ℝ)) ≤ B) :
    A - Real.log 4 * M * x ≤ B := by
  have h := mul_le_mul_of_nonneg_left (sum_prime_log_le hx) hM
  nlinarith

end SiegelZeros.W08

end OAI
