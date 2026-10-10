import OAI.Combinatorics.Progressions.Dynamics.SelectedParameterBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def kernelSamplerBudget (m : ℕ) (P : ℝ) : ℝ :=
  selectedFourierInputBudget m P + 3 * P + 64

theorem kernelSamplerBudget_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ kernelSamplerBudget m P := by
  unfold kernelSamplerBudget
  have h := selectedFourierInputBudget_nonneg m hP
  positivity

theorem le_kernelSamplerBudget (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    P ≤ kernelSamplerBudget m P := by
  unfold kernelSamplerBudget
  have h := le_selectedFourierInputBudget m hP
  linarith

theorem exists_kernelSamplerThreshold (m a : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ P : ℝ, 0 ≤ P →
      Real.exp (kernelSamplerBudget m P) ≤ Real.exp ((P + A)^A) ∧
      Real.exp ((kernelSamplerBudget m P + a)^a) ≤ Real.exp ((P + A)^A) := by
  let t : Polynomial ℕ := Polynomial.C m +
    (Polynomial.C (m+1) * (Polynomial.X+1)^(m+1) + 1)
  let q : Polynomial ℕ := (1+t^2)*(5*t+49)
  let b : Polynomial ℕ := q + 3 * Polynomial.X + 64
  let budget : Polynomial ℕ := b + (b + Polynomial.C a)^a
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget budget
  refine ⟨A, hA, ?_⟩
  intro P hP
  have hb := kernelSamplerBudget_nonneg m hP
  have hsum : kernelSamplerBudget m P + (kernelSamplerBudget m P + a)^a ≤ (P + A)^A := by
    simpa [budget, b, q, t, kernelSamplerBudget, selectedFourierInputBudget,
      selectedScaleDimensionBudget, geometricSiteBudget, allocatedScaleLog,
      Polynomial.eval₂_pow] using hbudget P hP
  constructor <;> apply Real.exp_le_exp.mpr
  · have hpow : 0 ≤ (kernelSamplerBudget m P + a)^a := by positivity
    linarith
  · linarith

end Erdos3.VectorPolynomial

end

end OAI
