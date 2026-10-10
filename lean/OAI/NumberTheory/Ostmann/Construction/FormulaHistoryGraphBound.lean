import OAI.NumberTheory.Ostmann.Construction.HistoryFormulaFourier
import OAI.NumberTheory.Ostmann.Arithmetic.ReconstructedDyadicGraph

namespace OAI

/-! # The supported graph estimate with all history polynomials constructed -/

namespace Ostmann

open scoped BigOperators SchwartzMap Classical

theorem formula_history_dyadic_graph_bound {J σ : Type*} [Fintype J] {n t : ℕ}
    (steps : List (HistoryPivotStep σ)) (frequencies : List ℤ) (C : ℕ) (hC : 1 ≤ C)
    (hfreq : ∀ s ∈ frequencies, s ≠ 0)
    (hsteps : ∀ step ∈ steps, step.s ∈ frequencies)
    (hsize : ∀ step ∈ steps, step.left.length + step.right.length + 4 ≤ C)
    (units : Fin steps.length → ℕ)
    (hunits : ∀ i, (units i : ℤ) ∣ (historyFrequencyBase frequencies : ℤ))
    (χ : (Bool ⊕ J) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (graph : (Bool ⊕ J) → (Bool ⊕ J) → ℤ)
    (unary : (Bool ⊕ J) → ℕ → ℂ) (outside : J → ℕ)
    (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : graph (.inl true) (.inl true) = 0 ∧ graph (.inl false) (.inl false) = 0)
    (hreverse : graph (.inl false) (.inl true) = 0)
    (P Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (hnonprincipal : ∀ q ∈ Q, χ (.inl true) q ^ graph (.inl true) (.inl false) ≠ 1)
    (A E : ℕ) (hA : 0 < A)
    (hMA : historyFrequencyPeriod frequencies (C ^ steps.length + 1) ≤ A)
    (hsmall : ∀ q ∈ Q, ∀ s ∈ frequencies, s.natAbs < q)
    (hlow : ∀ p ∈ P, 2 * A ≤ p) (hhigh : ∀ p ∈ P, p ≤ E)
    (b : ℝ) (hb : 0 < b) (hbQ : ∀ q ∈ Q, b ≤ (q : ℝ))
    (hPmass : 0 < ∑ p ∈ P, (p : ℝ)⁻¹) (hQmass : 0 < ∑ q ∈ Q, (q : ℝ)⁻¹)
    (fixed : Q → σ → ℤ) (coord : σ)
    (F : Fin n → HistoryFormula σ) (G : Fin t → HistoryFormula σ)
    (X : Fin n → ℝ) (ψ : 𝓢(ℝ, ℂ)) (v lo hi : Fin n → ℝ)
    (hlo : ∀ j, 1 ≤ lo j) (hhi : ∀ j, lo j ≤ hi j) (glo ghi : Fin t → ℝ)
    (Bq : ℕ) (hBq : ∀ q : Q, (q : ℕ) ≤ Bq) :
    let factors := fun q : Q => formulaFourierFactors F (fun j => (fixed q j : ℝ)) coord
      X ψ v lo hi hlo hhi
    let ranges := fun q : Q => formulaRangePolynomials G (fun j => (fixed q j : ℝ)) coord glo ghi
    let B := formulaFourierBudget ψ v lo hi
    let R := 3 * (∑ j, (F j).cost) + 2 * ∑ j, (G j).cost
    ‖∑ p : P, (primeSubsetPrior P P p : ℂ) *
      ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) *
        (finiteEdgeWeight (dirichletGraphEdge χ graph) unary
          (twoVertexLabels outside (q : ℕ) (p : ℕ)) *
          reconstructedHistoryAmplitude steps units (fixed q) coord (factors q)
            (fullHistoryPolynomials (factors q) (ranges q))
            (fullHistoryKeep (polynomialRangeKeep t)) (p : ℕ))‖ ^ 2 ≤
      ((Nat.log 2 E + 1 : ℕ) : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹) * (2 * B ^ 2) +
          (historyFrequencyPeriod frequencies (C ^ steps.length + 1) : ℝ) *
            ((3 ^ (2 * R) : ℕ) * (2 * (A : ℝ)⁻¹ * B ^ 2)) * (Bq : ℝ) ^ 2) := by
  dsimp only
  apply reconstructed_dyadic_graph_bound steps frequencies C hC hfreq hsteps hsize units hunits
    χ graph unary outside hunary hself hreverse P Q hprime hnonprincipal A E hA hMA hsmall
    hlow hhigh b hb hbQ hPmass hQmass fixed coord
  · exact formulaFourierBudget_nonneg ψ v lo hi hhi
  · intro q
    exact (formulaFourierFactors_budget F _ coord X ψ v lo hi hlo hhi).le
  · intro q
    exact formulaFourier_full_complexity F G _ coord X ψ v lo hi hlo hhi glo ghi
  · exact hBq

end Ostmann

end OAI
