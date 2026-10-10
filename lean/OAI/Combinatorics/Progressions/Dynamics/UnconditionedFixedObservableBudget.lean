import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget

namespace OAI

section

namespace Erdos3

theorem exists_unconditionedFixedObservableBudget (n₀ E : ℕ) :
    ∃ F : ℕ, 2 ≤ F ∧ ∀ p : ℝ, 0 ≤ p →
      (p + (n₀ : ℝ) + 4) ^ E ≤ (p + 2) ^ F := by
  obtain ⟨F, hF, hbound⟩ := exists_natPolynomial_fixed_power_budget
    ((Polynomial.X + Polynomial.C n₀ + 4) ^ E)
  refine ⟨F, hF, ?_⟩
  intro p hp
  simpa [Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

end OAI
