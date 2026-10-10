import OAI.NumberTheory.Ostmann.Preliminaries.UniformWindowStability

namespace OAI

open Erdos970

namespace Ostmann.Preliminaries
open scoped BigOperators

theorem uniformMass_complex_average {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (f : α → ℂ) :
    (∑ x, (uniformMass S x : ℂ) * f x) = (∑ x ∈ S, f x) / (S.card : ℂ) := by
  simp only [uniformMass, apply_ite, Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.ofReal_zero, ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter,
    ← Finset.mul_sum, div_eq_mul_inv]
  ring

theorem uniformWindow_complex_average (S : Set ℕ) (X : ℕ) (f : ℕ → ℂ) :
    (∑ i : upperWindow S X, (uniformWindowMass S X i : ℂ) * f i.val) =
      (∑ n ∈ upperWindow S X, f n) / ((upperWindow S X).card : ℂ) := by
  simp only [uniformWindowMass, Complex.ofReal_inv, Complex.ofReal_natCast,
    ← Finset.mul_sum, Finset.sum_coe_sort, div_eq_mul_inv]
  ring

end Ostmann.Preliminaries

end OAI
