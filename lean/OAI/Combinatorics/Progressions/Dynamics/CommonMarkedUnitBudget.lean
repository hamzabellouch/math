import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3

theorem exists_commonMarkedUnit_budget (a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + a) ^ a ≤ (p + C) ^ C ∧
      ((p + a) ^ a + b) ^ b ≤ (p + C) ^ C ∧
      ((p + a) ^ a + 3) ^ 3 ≤ (p + C) ^ C := by
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (P + (P + Polynomial.C b) ^ b + (P + 3) ^ 3)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hP : 0 ≤ (p + a) ^ a := by positivity
  have hQ : 0 ≤ ((p + a) ^ a + b) ^ b := by positivity
  have hS : 0 ≤ ((p + a) ^ a + 3) ^ 3 := by positivity
  have hsum : (p + a) ^ a + ((p + a) ^ a + b) ^ b + ((p + a) ^ a + 3) ^ 3 ≤
      (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith only [hsum, hQ, hS], by linarith only [hsum, hP, hS],
    by linarith only [hsum, hP, hQ]⟩

end Erdos3

end

end OAI
