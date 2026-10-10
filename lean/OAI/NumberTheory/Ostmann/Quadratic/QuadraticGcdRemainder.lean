import Mathlib.Algebra.Order.Chebyshev
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallMomentTransform

namespace OAI

/-! # Summing uniform pair remainders against the actual coefficients -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

theorem quadratic_pair_coefficient_mass (N : ℕ) (v : ℕ → ℂ) :
    (∑ z ∈ (oddSquarefreeRange N).product (oddSquarefreeRange N),
      ‖v z.1‖ * ‖v z.2‖) ≤ (N : ℝ) * quadraticSieveEnergy N v := by
  have he : (∑ z ∈ (oddSquarefreeRange N).product (oddSquarefreeRange N),
      ‖v z.1‖ * ‖v z.2‖) = (∑ n ∈ oddSquarefreeRange N, ‖v n‖) ^ 2 := by
    rw [Finset.product_eq_sprod, Finset.sum_product]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, pow_two]
  rw [he]
  calc
    _ ≤ ((oddSquarefreeRange N).card : ℝ) * quadraticSieveEnergy N v :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast oddSquarefreeRange_card_le N)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

noncomputable def quadraticGcdRemainder (N : ℕ) (v : ℕ → ℂ)
    (E : ℕ → ℕ × ℕ → ℂ) : ℂ :=
  ∑ D ∈ Finset.Icc 1 N, ∑ z ∈ quadraticGcdPairs N D,
    v z.1 * conj (v z.2) * E D z

theorem quadratic_gcd_remainder_bound (N : ℕ) (v : ℕ → ℂ)
    (E : ℕ → ℕ × ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T)
    (hE : ∀ D ∈ Finset.Icc 1 N, ∀ z ∈ quadraticGcdPairs N D, ‖E D z‖ ≤ T) :
    ‖quadraticGcdRemainder N v E‖ ≤ T * N * quadraticSieveEnergy N v := by
  unfold quadraticGcdRemainder
  calc
    _ ≤ ∑ D ∈ Finset.Icc 1 N, ∑ z ∈ quadraticGcdPairs N D,
        ‖v z.1‖ * ‖v z.2‖ * T := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro D hD
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro z hz
      simp only [norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left (hE D hD z hz) (by positivity)
    _ = T * ∑ z ∈ (oddSquarefreeRange N).product (oddSquarefreeRange N),
        ‖v z.1‖ * ‖v z.2‖ := by
      rw [← quadratic_pair_sum_gcd]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ ≤ T * ((N : ℝ) * quadraticSieveEnergy N v) :=
      mul_le_mul_of_nonneg_left (quadratic_pair_coefficient_mass N v) hT
    _ = _ := by ring

end Ostmann

end OAI
