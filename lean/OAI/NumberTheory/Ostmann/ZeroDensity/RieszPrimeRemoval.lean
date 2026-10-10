import OAI.NumberTheory.Ostmann.ZeroDensity.ArithmeticRieszMean
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothPrimePowerRemoval

namespace OAI

/-! # Higher prime powers in the literal Riesz mean -/

namespace Ostmann

open Complex
open scoped BigOperators

noncomputable def rieszPrimeMean (g : ℕ → ℂ) (X : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime,
    (Real.log n : ℂ) * g n * rieszPrimeTest (n / X)

theorem rieszTwistMean_sub (g h : ℕ → ℂ) (X : ℝ) :
    rieszTwistMean g X - rieszTwistMean h X = rieszTwistMean (fun n => g n - h n) X := by
  simp only [rieszTwistMean, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem rieszTwistMean_sub_prime (g : ℕ → ℂ) (X : ℝ) :
    rieszTwistMean g X - rieszPrimeMean g X =
      ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => ¬ n.Prime),
        (ArithmeticFunction.vonMangoldt n : ℂ) * g n * rieszPrimeTest (n / X) := by
  have hh := Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 ⌊X⌋₊) Nat.Prime
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * g n * rieszPrimeTest (n / X))
  have hp : (∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime,
      (ArithmeticFunction.vonMangoldt n : ℂ) * g n * rieszPrimeTest (n / X)) = rieszPrimeMean g X := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2]
  rw [hp] at hh
  change rieszPrimeMean g X + _ = rieszTwistMean g X at hh
  linear_combination -hh

theorem rieszTwistMean_prime_error (g : ℕ → ℂ) (X B : ℝ)
    (hX : 1 ≤ X) (hB : 0 ≤ B) (hg : ∀ n, ‖g n‖ ≤ B) :
    ‖rieszTwistMean g X - rieszPrimeMean g X‖ ≤ B * (2 * Real.sqrt X * Real.log X) := by
  rw [rieszTwistMean_sub_prime]
  calc
    _ ≤ ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => ¬ n.Prime),
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) * g n * rieszPrimeTest (n / X)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => ¬ n.Prime),
        B * ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      have hw := rieszPrimeTest_norm_le_one (n / X) (by positivity)
      calc
        _ ≤ (ArithmeticFunction.vonMangoldt n * B) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hg n) ArithmeticFunction.vonMangoldt_nonneg)
            hw (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ = B * (Chebyshev.psi X - Chebyshev.theta X) := by
      rw [← Finset.mul_sum, nonprime_mangoldt_sum]
    _ ≤ B * (2 * Real.sqrt X * Real.log X) := mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hX)) hB

end Ostmann

end OAI
