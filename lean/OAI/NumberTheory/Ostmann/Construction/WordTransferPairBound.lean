import OAI.NumberTheory.Ostmann.Construction.WordTransferCoefficient
import OAI.NumberTheory.Ostmann.Arithmetic.GuardedHistoryPair
import OAI.NumberTheory.Ostmann.Construction.DyadicGuardedGraph

namespace OAI

/-! # One-sided cancellation for two actual branching word histories -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem wordTransfer_pair_dyadic_bound {J σ : Type*} [Fintype J] {n : ℕ}
    (template template' : WordTransferTemplate σ n) (t t' : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (hn' : NonzeroInternalFrequencies n t')
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hwords' : template'.WordsBounded B)
    (hz : ∀ s ∈ allFrequencyList n t, s ≠ 0) (hz' : ∀ s ∈ allFrequencyList n t', s ≠ 0)
    (f f' : WordFourierParameters n)
    (χ : (Bool ⊕ J) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (graph : (Bool ⊕ J) → (Bool ⊕ J) → ℤ)
    (unary : (Bool ⊕ J) → ℕ → ℂ) (outside : J → ℕ)
    (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : graph (.inl true) (.inl true) = 0 ∧ graph (.inl false) (.inl false) = 0)
    (hreverse : graph (.inl false) (.inl true) = 0)
    (P Q : Finset ℕ) (hprime : ∀ q ∈ Q, q.Prime)
    (hnonprincipal : ∀ q ∈ Q, χ (.inl true) q ^ graph (.inl true) (.inl false) ≠ 1)
    (A E : ℕ) (hA : 0 < A)
    (hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
    (hsmall : ∀ q ∈ Q, ∀ s ∈ allFrequencyList n t, s.natAbs < q)
    (hsmall' : ∀ q ∈ Q, ∀ s ∈ allFrequencyList n t', s.natAbs < q)
    (hlow : ∀ p ∈ P, 2 * A ≤ p) (hhigh : ∀ p ∈ P, p ≤ E)
    (b : ℝ) (hb : 0 < b) (hbQ : ∀ q ∈ Q, b ≤ (q : ℝ))
    (hPmass : 0 < ∑ p ∈ P, (p : ℝ)⁻¹) (hQmass : 0 < ∑ q ∈ Q, (q : ℝ)⁻¹)
    (fixed : Q → σ → ℤ) (coord : σ) (Bq : ℕ) (hBq : ∀ q : Q, (q : ℕ) ≤ Bq) :
    let M := wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B
    let R := (3 * 2 ^ n + 3 * (2 ^ n - 1)) * B ^ (n + 1)
    let C := f.budget template t hn * f'.budget template' t' hn'
    ‖∑ p : P, (primeSubsetPrior P P p : ℂ) *
      ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) *
        (finiteEdgeWeight (dirichletGraphEdge χ graph) unary
          (twoVertexLabels outside (q : ℕ) (p : ℕ)) *
          (f.coefficient template t hn (Function.update (fixed q) coord (p : ℕ)) *
            conj (f'.coefficient template' t' hn' (Function.update (fixed q) coord (p : ℕ)))))‖ ^ 2 ≤
      ((Nat.log 2 E + 1 : ℕ) : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹) * (2 * C ^ 2) +
          (M : ℝ) * ((3 ^ (2 * (R + R)) : ℕ) * (2 * (A : ℝ)⁻¹ * C ^ 2)) * (Bq : ℝ) ^ 2) := by
  let M := wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B
  let R := (3 * 2 ^ n + 3 * (2 ^ n - 1)) * B ^ (n + 1)
  let G := template.guardAt t hn
  let G' := template'.guardAt t' hn'
  have hMpos : 0 < M := Nat.mul_pos (wordTransferFullPeriod_pos n t B hz)
    (wordTransferFullPeriod_pos n t' B hz')
  let : NeZero M := ⟨Nat.ne_of_gt hMpos⟩
  have hM (q : Q) : M.Coprime (q : ℕ) := by
    exact ((prime_coprime_wordTransferFullPeriod n t B q (hprime q q.property)
      (fun s hs => ⟨Int.natAbs_pos.mpr (hz s hs), hsmall q q.property s hs⟩)).mul_right
      (prime_coprime_wordTransferFullPeriod n t' B q (hprime q q.property)
        (fun s hs => ⟨Int.natAbs_pos.mpr (hz' s hs), hsmall' q q.property s hs⟩))).symm
  have hden (i : Fin ((2 ^ n - 1 + (2 ^ n - 1)) + (2 ^ n - 1 + (2 ^ n - 1)))) :
      Fin.append (wordGuardDenominators G) (wordGuardDenominators G') i ≠ 0 := by
    exact Fin.addCases (fun j => by simpa only [Fin.append_left] using template.guardAt_denominators_ne_zero t hn j)
      (fun j => by simpa only [Fin.append_right] using template'.guardAt_denominators_ne_zero t' hn' j) i
  have hdiv (i : Fin ((2 ^ n - 1 + (2 ^ n - 1)) + (2 ^ n - 1 + (2 ^ n - 1)))) :
      Fin.append (wordGuardDenominators G) (wordGuardDenominators G') i *
        ((Fin.append (wordGuardModuli G) (wordGuardModuli G') i : ℕ) : ℤ) ∣ (M : ℤ) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left, M, Nat.cast_mul] using
        (template.guardAt_full_period t hn B hB hwords j).trans (dvd_mul_right _ _)
    · simpa only [Fin.append_right, M, Nat.cast_mul] using
        (template'.guardAt_full_period t' hn' B hB hwords' j).trans (dvd_mul_left _ _)
  simp_rw [f.coefficient_local template t hn, f'.coefficient_local template' t' hn']
  simp_rw [← guardedHistoryAmplitude_pair]
  apply dyadic_guarded_graph_bound χ graph unary outside hunary hself hreverse P Q hprime
    hnonprincipal A E M hA hMA hM hlow hhigh b hb hbQ hPmass hQmass
  · exact fun _ => hden
  · exact fun _ => hdiv
  · exact mul_nonneg (f.budget_nonneg template t hn) (f'.budget_nonneg template' t' hn')
  · intro q
    rw [pairedPolynomialFactors_budget, f.factors_budget, f'.factors_budget]
  · intro q
    rw [polynomialWeightComplexity_pair]
    exact Nat.add_le_add (f.complexity_bound template t hn (fixed q) coord B hB hwords)
      (f'.complexity_bound template' t' hn' (fixed q) coord B hB hwords')
  · exact hBq

end Ostmann

end OAI
