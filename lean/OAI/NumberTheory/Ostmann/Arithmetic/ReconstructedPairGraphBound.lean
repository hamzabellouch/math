import OAI.NumberTheory.Ostmann.Arithmetic.GuardedHistoryPair
import OAI.NumberTheory.Ostmann.Construction.DyadicGuardedGraph

namespace OAI

/-! # Cancellation for two complete histories with their original common variables -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem reconstructed_pair_dyadic_graph_bound {J σ : Type*} [Fintype J] {n m t u : ℕ}
    (steps steps' : List (HistoryPivotStep σ)) (frequencies : List ℤ) (C : ℕ) (hC : 1 ≤ C)
    (hfreq : ∀ s ∈ frequencies, s ≠ 0)
    (hsteps : ∀ step ∈ steps, step.s ∈ frequencies)
    (hsteps' : ∀ step ∈ steps', step.s ∈ frequencies)
    (hsize : ∀ step ∈ steps, step.left.length + step.right.length + 4 ≤ C)
    (hsize' : ∀ step ∈ steps', step.left.length + step.right.length + 4 ≤ C)
    (units : Fin steps.length → ℕ) (units' : Fin steps'.length → ℕ)
    (hunits : ∀ i, (units i : ℤ) ∣ (historyFrequencyBase frequencies : ℤ))
    (hunits' : ∀ i, (units' i : ℤ) ∣ (historyFrequencyBase frequencies : ℤ))
    (χ : (Bool ⊕ J) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (graph : (Bool ⊕ J) → (Bool ⊕ J) → ℤ)
    (unary : (Bool ⊕ J) → ℕ → ℂ) (outside : J → ℕ)
    (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : graph (.inl true) (.inl true) = 0 ∧ graph (.inl false) (.inl false) = 0)
    (hreverse : graph (.inl false) (.inl true) = 0)
    (P Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (hnonprincipal : ∀ q ∈ Q, χ (.inl true) q ^ graph (.inl true) (.inl false) ≠ 1)
    (A E : ℕ) (hA : 0 < A)
    (hMA : historyFrequencyPeriod frequencies (C ^ (steps.length + steps'.length) + 1) ≤ A)
    (hsmall : ∀ q ∈ Q, ∀ s ∈ frequencies, s.natAbs < q)
    (hlow : ∀ p ∈ P, 2 * A ≤ p) (hhigh : ∀ p ∈ P, p ≤ E)
    (b : ℝ) (hb : 0 < b) (hbQ : ∀ q ∈ Q, b ≤ (q : ℝ))
    (hPmass : 0 < ∑ p ∈ P, (p : ℝ)⁻¹) (hQmass : 0 < ∑ q ∈ Q, (q : ℝ)⁻¹)
    (fixed : Q → σ → ℤ) (coord : σ)
    (F : Q → Fin n → ClippedPolynomialFactor) (G : Q → Fin m → ClippedPolynomialFactor)
    (H : Q → Fin t → Polynomial ℝ) (I : Q → Fin u → Polynomial ℝ)
    (keep : Q → (Fin t → Bool) → Bool) (keep' : Q → (Fin u → Bool) → Bool)
    (B B' : ℝ) (R R' Bq : ℕ) (hB : 0 ≤ B) (hB' : 0 ≤ B')
    (hbudget : ∀ q, smoothPolynomialBudget (F q) ≤ B)
    (hbudget' : ∀ q, smoothPolynomialBudget (G q) ≤ B')
    (hcomplexity : ∀ q, polynomialWeightComplexity (F q) (H q) ≤ R)
    (hcomplexity' : ∀ q, polynomialWeightComplexity (G q) (I q) ≤ R')
    (hBq : ∀ q : Q, (q : ℕ) ≤ Bq) :
    ‖∑ p : P, (primeSubsetPrior P P p : ℂ) *
      ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) *
        (finiteEdgeWeight (dirichletGraphEdge χ graph) unary
          (twoVertexLabels outside (q : ℕ) (p : ℕ)) *
          (reconstructedHistoryAmplitude steps units (fixed q) coord (F q) (H q) (keep q) (p : ℕ) *
            conj (reconstructedHistoryAmplitude steps' units' (fixed q) coord
              (G q) (I q) (keep' q) (p : ℕ))))‖ ^ 2 ≤
      ((Nat.log 2 E + 1 : ℕ) : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹) * (2 * (B * B') ^ 2) +
          (historyFrequencyPeriod frequencies (C ^ (steps.length + steps'.length) + 1) : ℝ) *
            ((3 ^ (2 * (R + R')) : ℕ) * (2 * (A : ℝ)⁻¹ * (B * B') ^ 2)) * (Bq : ℝ) ^ 2) := by
  let M := historyFrequencyPeriod frequencies (C ^ (steps.length + steps'.length) + 1)
  have hMpos : 0 < M := historyFrequencyPeriod_pos _ _ hfreq
  let : NeZero M := ⟨Nat.ne_of_gt hMpos⟩
  have hM (q : Q) : M.Coprime (q : ℕ) := by
    apply Nat.Coprime.symm
    apply prime_coprime_historyFrequencyPeriod frequencies _ _ (hprime q q.property)
    intro s hs
    exact ⟨Int.natAbs_pos.mpr (hfreq s hs), hsmall q q.property s hs⟩
  have hdiv (i : Fin (steps.length + steps'.length)) :
      Fin.append (fun i => (reconstructionFormulaAt steps .prime i).cleared.denominator)
          (fun i => (reconstructionFormulaAt steps' .prime i).cleared.denominator) i *
        ((Fin.append units units' i : ℕ) : ℤ) ∣ (M : ℤ) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using
        constructed_history_test_period_of_length steps frequencies C _ hC (by omega)
          hsteps hsize _ (hunits j) _ (reconstructionFormulaAt_mem steps .prime j)
    · simpa only [Fin.append_right] using
        constructed_history_test_period_of_length steps' frequencies C _ hC (by omega)
          hsteps' hsize' _ (hunits' j) _ (reconstructionFormulaAt_mem steps' .prime j)
  have hden (i : Fin (steps.length + steps'.length)) :
      Fin.append (fun i => (reconstructionFormulaAt steps .prime i).cleared.denominator)
        (fun i => (reconstructionFormulaAt steps' .prime i).cleared.denominator) i ≠ 0 := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using
        (reconstructionFormulaAt steps .prime j).cleared.denominator_ne_zero
    · simpa only [Fin.append_right] using
        (reconstructionFormulaAt steps' .prime j).cleared.denominator_ne_zero
  simp_rw [reconstructedHistoryAmplitude_pair]
  apply dyadic_guarded_graph_bound χ graph unary outside hunary hself hreverse P Q hprime
    hnonprincipal A E M hA hMA hM hlow hhigh b hb hbQ hPmass hQmass
  · exact fun _ => hden
  · exact fun _ => hdiv
  · exact mul_nonneg hB hB'
  · intro q
    rw [pairedPolynomialFactors_budget]
    exact mul_le_mul (hbudget q) (hbudget' q) (smoothPolynomialBudget_nonneg _) hB
  · intro q
    rw [polynomialWeightComplexity_pair]
    exact Nat.add_le_add (hcomplexity q) (hcomplexity' q)
  · exact hBq

end Ostmann

end OAI
