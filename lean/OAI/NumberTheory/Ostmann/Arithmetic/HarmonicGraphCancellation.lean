import OAI.NumberTheory.Ostmann.ZeroDensity.DirichletGraphFactor
import OAI.NumberTheory.Ostmann.Arithmetic.HarmonicOneSidedBound

namespace OAI

/-! # Applying the one-sided estimate to the actual graph quotient -/

namespace Ostmann

open scoped BigOperators Classical

theorem harmonic_one_sided_graph_bound {J : Type*} [Fintype J]
    (χ : (Bool ⊕ J) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : (Bool ⊕ J) → (Bool ⊕ J) → ℤ)
    (unary : (Bool ⊕ J) → ℕ → ℂ) (fixed : J → ℕ)
    (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : b (.inl true) (.inl true) = 0 ∧ b (.inl false) (.inl false) = 0)
    (hreverse : b (.inl false) (.inl true) = 0)
    (P Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (hnonprincipal : ∀ q ∈ Q, χ (.inl true) q ^ b (.inl true) (.inl false) ≠ 1)
    (a M K : ℕ) (ha : 0 < a) (hM : ∀ q : Q, M.Coprime (q : ℕ))
    (hlow : ∀ p ∈ P, a ≤ p) (hhigh : ∀ p ∈ P, p < a + K * M)
    (b₀ : ℝ) (hb₀ : 0 < b₀) (hbQ : ∀ q ∈ Q, b₀ ≤ (q : ℝ))
    (hPmass : 0 < ∑ p ∈ P, (p : ℝ)⁻¹) (hQmass : 0 < ∑ q ∈ Q, (q : ℝ)⁻¹)
    {n t : ℕ} (F : Q → Fin n → ClippedPolynomialFactor)
    (H : Q → Fin t → Polynomial ℝ) (keep : Q → (Fin t → Bool) → Bool)
    (B : ℝ) (R Bq : ℕ) (hB : 0 ≤ B)
    (hbudget : ∀ q, smoothPolynomialBudget (F q) ≤ B)
    (hcomplexity : ∀ q, polynomialWeightComplexity (F q) (H q) ≤ R)
    (hBq : ∀ q : Q, (q : ℕ) ≤ Bq) :
    ‖∑ p : P, (primeSubsetPrior P P p : ℂ) *
      ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) *
        (finiteEdgeWeight (dirichletGraphEdge χ b) unary
          (twoVertexLabels fixed (q : ℕ) (p : ℕ)) *
          polynomialAmplitude (F q) (H q) (keep q) (p : ℝ))‖ ^ 2 ≤
      (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b₀⁻¹) * (((K * M : ℕ) : ℝ) / a * B ^ 2) +
          (M : ℝ) * ((3 ^ (2 * R) : ℕ) * (2 * (a : ℝ)⁻¹ * B ^ 2)) * (Bq : ℝ) ^ 2) := by
  have hQne : Q.Nonempty := by
    by_contra h
    have he : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he, Finset.sum_empty] at hQmass
    exact (lt_irrefl (0 : ℝ)) hQmass
  obtain ⟨q₀, hq₀⟩ := hQne
  have hforward : b (.inl true) (.inl false) ≠ 0 := by
    intro h
    have hh := hnonprincipal q₀ hq₀
    simp only [h, zpow_zero, ne_eq, not_true_eq_false] at hh
  obtain ⟨U, V, hU, hV, hfactor⟩ := dirichlet_one_sided_graph_factorization
    χ b unary fixed hunary hself hreverse hforward
  have hb := harmonic_polynomial_one_sided_bound P Q hprime
    (fun q => χ (.inl true) q ^ b (.inl true) (.inl false))
    (fun q => hnonprincipal q q.property) a M K ha hM hlow hhigh b₀ hb₀ hbQ hPmass hQmass
    F H keep B R Bq hB hbudget hcomplexity hBq
    (fun p => U p) (fun q => V q) (fun p => hU p) (fun q => hV q)
  have he : (∑ p : P, (primeSubsetPrior P P p : ℂ) *
      ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) *
        (finiteEdgeWeight (dirichletGraphEdge χ b) unary
          (twoVertexLabels fixed (q : ℕ) (p : ℕ)) *
          polynomialAmplitude (F q) (H q) (keep q) (p : ℝ))) =
      ∑ p : P, (primeSubsetPrior P P p : ℂ) *
        (U p * ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) * V q *
          ((χ (.inl true) q ^ b (.inl true) (.inl false)) ((p : ℕ) : ZMod (q : ℕ)) *
            polynomialAmplitude (F q) (H q) (keep q) (p : ℝ))) := by
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [hfactor]
    ring
  rw [he]
  exact hb

end Ostmann

end OAI
