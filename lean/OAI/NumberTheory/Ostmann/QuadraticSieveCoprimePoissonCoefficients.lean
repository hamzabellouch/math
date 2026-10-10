import Mathlib.Data.Nat.Totient
import OAI.NumberTheory.Ostmann.QuadraticSieveGcdSeparation

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped ArithmeticFunction.Moebius

theorem sum_moebius_div_divisors (k : ℕ) (hk : 0 < k) :
    (∑ d ∈ k.divisors, (μ d : ℂ) / (d : ℂ)) = (Nat.totient k : ℂ) / (k : ℂ) := by
  have htot : ∀ n : ℕ, 0 < n → (∑ d ∈ n.divisors, (Nat.totient d : ℂ)) = (n : ℂ) := by
    intro n hn
    exact_mod_cast Nat.sum_totient n
  have hi := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp htot k hk
  rw [Nat.sum_divisorsAntidiagonal (fun x y : ℕ => (μ x : ℂ) * (y : ℂ))] at hi
  rw [← hi, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne'
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd0]
  field_simp

theorem sum_moebius_large_eq_neg_small (k : ℕ) (hk : 2 ≤ k) (Y : ℝ) :
    (∑ d ∈ k.divisors.filter (fun d : ℕ => Y < (d : ℝ)), (μ d : ℂ)) =
      -∑ d ∈ k.divisors.filter (fun d : ℕ => (d : ℝ) ≤ Y), (μ d : ℂ) := by
  classical
  have hzero : (∑ d ∈ k.divisors, (μ d : ℂ)) = 0 := by
    rw [sum_moebius_divisors_complex, ite_eq_right (by omega)]
  have hsum := Finset.sum_filter_add_sum_filter_not
    (s := k.divisors) (p := fun d : ℕ => (d : ℝ) ≤ Y) (f := fun d => (μ d : ℂ))
  simp only [not_le] at hsum
  rw [hzero] at hsum
  linear_combination hsum

end Ostmann.QuadraticSieve

end OAI
