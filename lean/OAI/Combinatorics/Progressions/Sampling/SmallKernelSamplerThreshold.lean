import OAI.Combinatorics.Progressions.Dynamics.SelectedParameterBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def smallKernelSamplerBudget (m : ℕ) (P : ℝ) : ℝ :=
  selectedFourierInputBudget m P + 4 * P + 128

theorem smallKernelSamplerBudget_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ smallKernelSamplerBudget m P := by
  unfold smallKernelSamplerBudget
  have h := selectedFourierInputBudget_nonneg m hP
  positivity

theorem le_smallKernelSamplerBudget (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    P ≤ smallKernelSamplerBudget m P := by
  unfold smallKernelSamplerBudget
  have h := le_selectedFourierInputBudget m hP
  linarith

theorem exists_smallKernelSamplerThreshold (m a : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ P : ℝ, 0 ≤ P →
      Real.exp (smallKernelSamplerBudget m P) ≤ Real.exp ((P + A)^A) ∧
      Real.exp ((smallKernelSamplerBudget m P + a)^a) ≤ Real.exp ((P + A)^A) := by
  let t : Polynomial ℕ := Polynomial.C m +
    (Polynomial.C (m+1) * (Polynomial.X+1)^(m+1) + 1)
  let q : Polynomial ℕ := (1+t^2)*(5*t+49)
  let b : Polynomial ℕ := q + 4 * Polynomial.X + 128
  let budget : Polynomial ℕ := b + (b + Polynomial.C a)^a
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget budget
  refine ⟨A, hA, ?_⟩
  intro P hP
  have hb := smallKernelSamplerBudget_nonneg m hP
  have hsum : smallKernelSamplerBudget m P + (smallKernelSamplerBudget m P + a)^a ≤ (P + A)^A := by
    simpa [budget, b, q, t, smallKernelSamplerBudget, selectedFourierInputBudget,
      selectedScaleDimensionBudget, geometricSiteBudget, allocatedScaleLog,
      Polynomial.eval₂_pow] using hbudget P hP
  constructor <;> apply Real.exp_le_exp.mpr
  · have hpow : 0 ≤ (smallKernelSamplerBudget m P + a)^a := by positivity
    linarith
  · linarith

end Erdos3.VectorPolynomial

end

end OAI
