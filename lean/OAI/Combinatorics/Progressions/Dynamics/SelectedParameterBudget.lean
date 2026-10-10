import OAI.Combinatorics.Progressions.Fourier.AllocatedMaskedCoefficientFourier

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_selectedParameterThreshold (m a : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ P : ℝ, 0 ≤ P →
      Real.exp ((selectedFourierInputBudget m P + a)^a) ≤ Real.exp ((P+A)^A) := by
  let t : Polynomial ℕ := Polynomial.C m +
    (Polynomial.C (m+1) * (Polynomial.X+1)^(m+1) + 1)
  let q : Polynomial ℕ := (1+t^2)*(5*t+49)
  let budget : Polynomial ℕ := (q+Polynomial.C a)^a
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget budget
  refine ⟨A, hA, ?_⟩
  intro P hP
  apply Real.exp_le_exp.mpr
  simpa [budget, q, t, selectedFourierInputBudget, selectedScaleDimensionBudget,
    geometricSiteBudget, allocatedScaleLog, Polynomial.eval₂_pow] using hbudget P hP

end Erdos3.VectorPolynomial

end

end OAI
