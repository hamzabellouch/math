import OAI.NumberTheory.Ostmann.Construction.WordUnitCoefficient
import OAI.NumberTheory.Ostmann.Arithmetic.GuardedHistoryPair
import OAI.NumberTheory.Ostmann.Construction.DyadicGuardedGraph

namespace OAI

/-! # One-sided cancellation with every original word and product range -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

private theorem append_nonzero {r s : ℕ} (d : Fin r → ℤ) (e : Fin s → ℤ)
    (hd : ∀ i, d i ≠ 0) (he : ∀ i, e i ≠ 0) : ∀ i, Fin.append d e i ≠ 0 := by
  intro i
  exact Fin.addCases (fun j => by simpa only [Fin.append_left] using hd j)
    (fun j => by simpa only [Fin.append_right] using he j) i

private theorem append_test_dvd {r s : ℕ} (d : Fin r → ℤ) (e : Fin s → ℤ)
    (v : Fin r → ℕ) (w : Fin s → ℕ) (M : ℤ)
    (hd : ∀ i, d i * (v i : ℤ) ∣ M) (he : ∀ i, e i * (w i : ℤ) ∣ M) :
    ∀ i, Fin.append d e i * ((Fin.append v w i : ℕ) : ℤ) ∣ M := by
  intro i
  exact Fin.addCases (fun j => by simpa only [Fin.append_left] using hd j)
    (fun j => by simpa only [Fin.append_right] using he j) i

theorem unitRangedWordTransfer_pair_dyadic_bound {J σ : Type*} [Fintype J] {n : ℕ}
    (template template' : WordTransferTemplate σ n)
    (U U' D D' : WordRangeDecoration σ n) (t t' : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (hn' : NonzeroInternalFrequencies n t')
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hwords' : template'.WordsBounded B)
    (hD : D.WordsBounded B) (hD' : D'.WordsBounded B)
    (hU : U.WordsBounded B) (hU' : U'.WordsBounded B)
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
    let R := (3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)
    let C := f.budget template t hn * f'.budget template' t' hn'
    ‖∑ p : P, (primeSubsetPrior P P p : ℂ) *
      ∑ q : Q, (primeSubsetPrior Q Q q : ℂ) *
        (finiteEdgeWeight (dirichletGraphEdge χ graph) unary
          (twoVertexLabels outside (q : ℕ) (p : ℕ)) *
          (f.unitRangedCoefficient U D template t hn (Function.update (fixed q) coord (p : ℕ)) *
            conj (f'.unitRangedCoefficient U' D' template' t' hn' (Function.update (fixed q) coord (p : ℕ)))))‖ ^ 2 ≤
      ((Nat.log 2 E + 1 : ℕ) : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)⁻¹ *
        (((∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ * b⁻¹) * (2 * C ^ 2) +
          (M : ℝ) * ((3 ^ (2 * (R + R)) : ℕ) * (2 * (A : ℝ)⁻¹ * C ^ 2)) * (Bq : ℝ) ^ 2) := by
  let M := wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B
  let R := (3 * 2 ^ n + 3 * (2 ^ n - 1) + 2 * (D.count + D'.count)) * B ^ (n + 1)
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
  let UG := U.unitAt template t hn
  let UG' := U'.unitAt template' t' hn'
  let d1 := Fin.append (wordGuardDenominators G) (wordUnitDenominators UG)
  let d2 := Fin.append (wordGuardDenominators G') (wordUnitDenominators UG')
  let s1 := Fin.append (wordGuardModuli G) (wordUnitModuli UG)
  let s2 := Fin.append (wordGuardModuli G') (wordUnitModuli UG')
  have hd1 : ∀ i, d1 i ≠ 0 := append_nonzero _ _
    (template.guardAt_denominators_ne_zero t hn) (fun i => (UG i).formula.cleared.denominator_ne_zero)
  have hd2 : ∀ i, d2 i ≠ 0 := append_nonzero _ _
    (template'.guardAt_denominators_ne_zero t' hn') (fun i => (UG' i).formula.cleared.denominator_ne_zero)
  have hden := append_nonzero d1 d2 hd1 hd2
  have hdiv1 : ∀ i, d1 i * (s1 i : ℤ) ∣ (M : ℤ) := by
    apply append_test_dvd
    · intro i
      exact (template.guardAt_full_period t hn B hB hwords i).trans
        (by exact_mod_cast dvd_mul_right (wordTransferFullPeriod n t B) (wordTransferFullPeriod n t' B))
    · intro i
      exact (U.unitAt_period template t hn B hB hwords hU i).trans
        (by exact_mod_cast dvd_mul_right (wordTransferFullPeriod n t B) (wordTransferFullPeriod n t' B))
  have hdiv2 : ∀ i, d2 i * (s2 i : ℤ) ∣ (M : ℤ) := by
    apply append_test_dvd
    · intro i
      exact (template'.guardAt_full_period t' hn' B hB hwords' i).trans
        (by exact_mod_cast dvd_mul_left (wordTransferFullPeriod n t' B) (wordTransferFullPeriod n t B))
    · intro i
      exact (U'.unitAt_period template' t' hn' B hB hwords' hU' i).trans
        (by exact_mod_cast dvd_mul_left (wordTransferFullPeriod n t' B) (wordTransferFullPeriod n t B))
  have hdiv := append_test_dvd d1 d2 s1 s2 (M : ℤ) hdiv1 hdiv2
  simp_rw [f.unitRangedCoefficient_local U D template t hn, f'.unitRangedCoefficient_local U' D' template' t' hn']
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
    have hleft := f.ranged_complexity_bound D template t hn (fixed q) coord B hB hwords hD
    have hright := f'.ranged_complexity_bound D' template' t' hn' (fixed q) coord B hB hwords' hD'
    apply Nat.add_le_add
    · apply hleft.trans
      apply Nat.mul_le_mul_right
      omega
    · apply hright.trans
      apply Nat.mul_le_mul_right
      omega

  · exact hBq

end Ostmann

end OAI
