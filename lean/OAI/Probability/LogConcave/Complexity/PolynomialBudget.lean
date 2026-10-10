import Mathlib

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped BigOperators

def polynomialBudget (P : Polynomial ℝ) : ℝ := ∑n ∈ P.support,|P.coeff n|

lemma polynomialBudget_nonneg (P : Polynomial ℝ) : 0≤polynomialBudget P :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

lemma eval_abs_le_polynomialBudget (P : Polynomial ℝ) {ρ : ℝ} (h0 : 0≤ρ) (h1 : ρ≤1) :
    |P.eval ρ|≤polynomialBudget P := by
  rw [Polynomial.eval_eq_sum]
  unfold Polynomial.sum polynomialBudget
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro n _
  rw [abs_mul,abs_pow,abs_of_nonneg h0]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ h0 h1)

lemma scaledCoefficient_bound (P : Polynomial ℝ) (n : ℕ) {r L ρ : ℝ}
    (hl0 : 0≤r*L) (hl1 : r*L≤1) (h0 : 0≤ρ) (h1 : ρ≤1) :
    |(r*L)^n*P.eval ρ|≤polynomialBudget P := by
  rw [abs_mul,abs_pow,abs_of_nonneg hl0]
  exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hl0 hl1) (abs_nonneg _)).trans
    (by simpa using eval_abs_le_polynomialBudget P h0 h1)
end LogConcaveSampling

end

end

end

end OAI
