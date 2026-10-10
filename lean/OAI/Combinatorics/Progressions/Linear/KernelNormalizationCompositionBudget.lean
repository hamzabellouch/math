import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

theorem exists_kernelNormalization_composition_budget (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      p + (p + 2) ^ 2 + ((p + 2) ^ 4 + (a : ℝ)) ^ a ≤ (p + C) ^ C := by
  let P : Polynomial ℕ := Polynomial.X + (Polynomial.X + 2) ^ 2 +
    ((Polynomial.X + 2) ^ 4 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [P, Polynomial.eval₂_pow] using hbound p hp

theorem exists_kernelNormalization_composition_power_budget (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      ((p + 2) ^ 4 + (a : ℝ)) ^ a ≤ (p + C) ^ C := by
  obtain ⟨C, hC, hbound⟩ := exists_kernelNormalization_composition_budget a
  refine ⟨C, hC, ?_⟩
  intro p hp
  exact (le_add_of_nonneg_left (add_nonneg hp (sq_nonneg (p + 2)))).trans (hbound p hp)

end Erdos3

end

end OAI
