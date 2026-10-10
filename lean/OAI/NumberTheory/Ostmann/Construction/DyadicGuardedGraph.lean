import OAI.NumberTheory.Ostmann.ZeroDensity.DirichletGraphFactor
import OAI.NumberTheory.Ostmann.Construction.DyadicGuardedHistory

namespace OAI

/-! # Whole-range one-sided cancellation for the supported quotient graph -/

namespace Ostmann

open scoped BigOperators Classical

theorem dyadic_guarded_graph_bound {J σ I : Type*} [Fintype J] [Fintype I] {n t : ℕ}
    (χ : (Bool ⊕ J) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (graph : (Bool ⊕ J) → (Bool ⊕ J) → ℤ)
    (unary : (Bool ⊕ J) → ℕ → ℂ) (outside : J → ℕ)
    (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : graph (.inl true) (.inl true) = 0 ∧ graph (.inl false) (.inl false) = 0)
    (hreverse : graph (.inl false) (.inl true) = 0)
    (P Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (hnonprincipal : ∀ q ∈ Q, χ (.inl true) q ^ graph (.inl true) (.inl false) ≠ 1)
    (A E M : ℕ) [NeZero M] (hA : 0 < A) (hMA : M ≤ A)
    (hM : ∀ q : Q, M.Coprime (q : ℕ))
    (hlow : ∀ p ∈ P, 2 * A ≤ p) (hhigh : ∀ p ∈ P, p ≤ E)
    (b : ℝ) (hb : 0 < b) (hbQ : ∀ q ∈ Q, b ≤ (q : ℝ))
    (hPmass : 0 < ∑ p ∈ P, (p : ℝ)⁻¹) (hQmass : 0 < ∑ q ∈ Q, (q : ℝ)⁻¹)
    (N : Q → I → MvPolynomial σ ℤ) (d : Q → I → ℤ) (s : Q → I → ℕ)
    (fixed : Q → σ → ℤ) (coord : σ)
    (hd : ∀ q j, d q j ≠ 0) (hdiv : ∀ q j, d q j * s q j ∣ (M : ℤ))
    (F : Q → Fin n → ClippedPolynomialFactor) (H : Q → Fin t → Polynomial ℝ)
    (keep : Q → (Fin t → Bool) → Bool) (B : ℝ) (R Bq : ℕ)
    (hB : 0 ≤ B) (hbudget : ∀ q, smoothPolynomialBudget (F q) ≤ B)
    (hcomplexity : ∀ q, polynomialWeightComplexity (F q) (H q) ≤ R)
    (hBq : ∀ q : Q, (q : ℕ) ≤ Bq) :
    ‖∑ p : P, (primeSubsetPrior P P p : ℂ) *
      ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) *
        (finiteEdgeWeight (dirichletGraphEdge χ graph) unary
          (twoVertexLabels outside (q : ℕ) (p : ℕ)) *
          guardedHistoryAmplitude (N q) (d q) (s q) (fixed q) coord (F q) (H q) (keep q) (p : ℕ))‖ ^ 2 ≤
      ((Nat.log 2 E + 1 : ℕ) : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹) * (2 * B ^ 2) +
          (M : ℝ) * ((3 ^ (2 * R) : ℕ) * (2 * (A : ℝ)⁻¹ * B ^ 2)) * (Bq : ℝ) ^ 2) := by
  have hQne : Q.Nonempty := by
    by_contra h
    have he : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he, Finset.sum_empty] at hQmass
    exact (lt_irrefl (0 : ℝ)) hQmass
  obtain ⟨q₀, hq₀⟩ := hQne
  have hforward : graph (.inl true) (.inl false) ≠ 0 := by
    intro h
    have hh := hnonprincipal q₀ hq₀
    simp only [h, zpow_zero, ne_eq, not_true_eq_false] at hh
  obtain ⟨U, V, hU, hV, hfactor⟩ := dirichlet_one_sided_graph_factorization
    χ graph unary outside hunary hself hreverse hforward
  have hbound := dyadic_guarded_history_bound P Q hprime
    (fun q => χ (.inl true) q ^ graph (.inl true) (.inl false))
    (fun q => hnonprincipal q q.property) A E M hA hMA hM hlow hhigh b hb hbQ hPmass hQmass
    N d s fixed coord hd hdiv F H keep B R Bq hB hbudget hcomplexity hBq U (fun q => V q)
    (fun p _ => hU p) (fun q => hV q)
  have he : (∑ p : P, (primeSubsetPrior P P p : ℂ) *
      ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) *
        (finiteEdgeWeight (dirichletGraphEdge χ graph) unary
          (twoVertexLabels outside (q : ℕ) (p : ℕ)) *
          guardedHistoryAmplitude (N q) (d q) (s q) (fixed q) coord (F q) (H q) (keep q) (p : ℕ))) =
      ∑ p : P, (primeSubsetPrior P P p : ℂ) *
        (U p * ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) * V q *
          ((χ (.inl true) q ^ graph (.inl true) (.inl false)) ((p : ℕ) : ZMod (q : ℕ)) *
            guardedHistoryAmplitude (N q) (d q) (s q) (fixed q) coord (F q) (H q) (keep q) (p : ℕ))) := by
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [hfactor]
    ring
  rw [he]
  exact hbound

end Ostmann

end OAI
