import OAI.Combinatorics.Progressions.Estimates.CocycleHorizontalNormalization

namespace OAI

section

open scoped Matrix

namespace Erdos3

open VectorPolynomial

theorem exists_controlled_polynomial_splitting
    {ι κ σ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (e r : VectorPolynomial σ ℚ (ι → ℝ)) (v : VectorPolynomial σ ℚ (κ → ℝ))
    (he0 : coefficients e 0 = 0) (hr0 : coefficients r 0 = 0)
    (he : ∀ α, α ≠ 0 → ‖coefficients e α‖ ≤ Real.exp p / monomialScale T α)
    (hr : ∀ α, coefficients r α ∈ realDenominatorGrid l)
    (hv : realMatrixPolynomialMap A v = e + r) :
    ∃ (u b : VectorPolynomial σ ℚ (κ → ℝ)) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      realMatrixPolynomialMap A u = e ∧ realMatrixPolynomialMap A b = r ∧
      coefficients u 0 = 0 ∧ coefficients b 0 = 0 ∧
      (∀ α, ‖coefficients u α‖ ≤ Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, coefficients b α ∈ realDenominatorGrid m) ∧
      realMatrixPolynomialMap A (v - u - b) = 0 ∧
      (∀ w d, DegreeLE w d e → DegreeLE w d u) ∧
      (∀ w d, DegreeLE w d r → DegreeLE w d b) := by
  obtain ⟨S, m, hm, hmp, hS⟩ :=
    exists_controlled_linear_splitting A hH hl hA hp hι hκ hHp hlp T hT
  have hS0 : (fun i j => (S i j : ℝ)) *ᵥ (0 : ι → ℝ) = 0 := Matrix.mulVec_zero _
  have hA0 : (fun i j => (A i j : ℝ)) *ᵥ (0 : κ → ℝ) = 0 := Matrix.mulVec_zero _
  have hvα (α : σ →₀ ℕ) :
      (fun i j => (A i j : ℝ)) *ᵥ coefficients v α = coefficients e α + coefficients r α := by
    have h := congrArg (fun q => coefficients q α) hv
    simpa only [coefficients_realMatrixPolynomialMap, map_add, Finsupp.add_apply] using h
  have hsplit (α : σ →₀ ℕ) (hα : α ≠ 0) :=
    hS α hα (coefficients e α) (coefficients r α) (coefficients v α)
      (he α hα) (hr α) (hvα α)
  have heu : realMatrixPolynomialMap A (realMatrixPolynomialMap S e) = e := by
    apply coefficients.injective
    apply Finsupp.ext
    intro α
    simp only [coefficients_realMatrixPolynomialMap]
    by_cases hα : α = 0
    · simp only [hα, he0, hS0, hA0]
    · exact (hsplit α hα).1
  have hrb : realMatrixPolynomialMap A (realMatrixPolynomialMap S r) = r := by
    apply coefficients.injective
    apply Finsupp.ext
    intro α
    simp only [coefficients_realMatrixPolynomialMap]
    by_cases hα : α = 0
    · simp only [hα, hr0, hS0, hA0]
    · exact (hsplit α hα).2.1
  refine ⟨realMatrixPolynomialMap S e, realMatrixPolynomialMap S r, m, hm, hmp, heu, hrb,
    by simp only [coefficients_realMatrixPolynomialMap, he0, hS0],
    by simp only [coefficients_realMatrixPolynomialMap, hr0, hS0], ?_, ?_, ?_, ?_, ?_⟩
  · intro α
    rw [coefficients_realMatrixPolynomialMap]
    by_cases hα : α = 0
    · subst α
      simpa only [he0, hS0, norm_zero, monomialScale_zero, div_one] using
        (Real.exp_nonneg ((p + 2) ^ 18 + p))
    · exact (hsplit α hα).2.2.1
  · intro α
    rw [coefficients_realMatrixPolynomialMap]
    by_cases hα : α = 0
    · subst α
      rw [hr0, hS0]
      exact ⟨0, by ext i; simp⟩
    · exact (hsplit α hα).2.2.2.1
  · rw [map_sub, map_sub, hv, heu, hrb]
    abel
  · intro w d h
    exact degreeLE_realMatrixPolynomialMap S h
  · intro w d h
    exact degreeLE_realMatrixPolynomialMap S h

end Erdos3

end

end OAI
