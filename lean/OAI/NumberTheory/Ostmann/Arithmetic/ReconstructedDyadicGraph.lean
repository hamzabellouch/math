import OAI.NumberTheory.Ostmann.Construction.ConstructedHistoryGuards
import OAI.NumberTheory.Ostmann.Construction.DyadicGuardedGraph

namespace OAI

/-! # One-sided graph cancellation for the original reconstructed history support -/

namespace Ostmann

open scoped BigOperators Classical

theorem reconstructed_dyadic_graph_bound {J σ : Type*} [Fintype J] {n t : ℕ}
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
    (F : Q → Fin n → ClippedPolynomialFactor) (H : Q → Fin t → Polynomial ℝ)
    (keep : Q → (Fin t → Bool) → Bool) (B : ℝ) (R Bq : ℕ)
    (hB : 0 ≤ B) (hbudget : ∀ q, smoothPolynomialBudget (F q) ≤ B)
    (hcomplexity : ∀ q, polynomialWeightComplexity (F q) (H q) ≤ R)
    (hBq : ∀ q : Q, (q : ℕ) ≤ Bq) :
    ‖∑ p : P, (primeSubsetPrior P P p : ℂ) *
      ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) *
        (finiteEdgeWeight (dirichletGraphEdge χ graph) unary
          (twoVertexLabels outside (q : ℕ) (p : ℕ)) *
          reconstructedHistoryAmplitude steps units (fixed q) coord (F q) (H q) (keep q) (p : ℕ))‖ ^ 2 ≤
      ((Nat.log 2 E + 1 : ℕ) : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹) * (2 * B ^ 2) +
          (historyFrequencyPeriod frequencies (C ^ steps.length + 1) : ℝ) *
            ((3 ^ (2 * R) : ℕ) * (2 * (A : ℝ)⁻¹ * B ^ 2)) * (Bq : ℝ) ^ 2) := by
  let M := historyFrequencyPeriod frequencies (C ^ steps.length + 1)
  have hMpos : 0 < M := historyFrequencyPeriod_pos _ _ hfreq
  let : NeZero M := ⟨Nat.ne_of_gt hMpos⟩
  have hM (q : Q) : M.Coprime (q : ℕ) := by
    apply Nat.Coprime.symm
    apply prime_coprime_historyFrequencyPeriod frequencies _ _ (hprime q q.property)
    intro s hs
    exact ⟨Int.natAbs_pos.mpr (hfreq s hs), hsmall q q.property s hs⟩
  have hdiv (i : Fin steps.length) :
      (reconstructionFormulaAt steps .prime i).cleared.denominator * (units i : ℤ) ∣ (M : ℤ) :=
    constructed_history_test_period_of_dvd steps frequencies C hC hsteps hsize
      _ (hunits i) _ (reconstructionFormulaAt_mem steps .prime i)
  simp_rw [reconstructedHistoryAmplitude_exact]
  exact dyadic_guarded_graph_bound χ graph unary outside hunary hself hreverse
    P Q hprime hnonprincipal A E M hA hMA hM hlow hhigh b hb hbQ hPmass hQmass
    (fun _ i => (reconstructionFormulaAt steps .prime i).cleared.numerator)
    (fun _ i => (reconstructionFormulaAt steps .prime i).cleared.denominator)
    (fun _ => units) fixed coord
    (fun _ i => (reconstructionFormulaAt steps .prime i).cleared.denominator_ne_zero)
    (fun _ => hdiv) F H keep B R Bq hB hbudget hcomplexity hBq

end Ostmann

end OAI
