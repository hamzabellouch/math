import OAI.NumberTheory.Ostmann.Arithmetic.UnitRangedOriginalPair
import OAI.NumberTheory.Ostmann.Construction.FixedPivotTwoCoordinates

namespace OAI

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- Every remaining coordinate keeps its own original harmonic prior.
Only the displayed numerical estimate remains to be specialized. -/
theorem fixed_pivot_unit_ranged_original_pair_bound {V : Type*} [Fintype V]
    (a b : V) (hab : a ≠ b) {n : ℕ}
    (template template' : WordTransferTemplate (ExpandedScheduledVariable (Option V) n) n)
    (U U' D D' : WordRangeDecoration (ExpandedScheduledVariable (Option V) n) n) (t t' : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (hn' : NonzeroInternalFrequencies n t')
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hwords' : template'.WordsBounded B)
    (hD : D.WordsBounded B) (hD' : D'.WordsBounded B)
    (hU : U.WordsBounded B) (hU' : U'.WordsBounded B)
    (hz : ∀ s ∈ allFrequencyList n t, s ≠ 0) (hz' : ∀ s ∈ allFrequencyList n t', s ≠ 0)
    (f f' : WordFourierParameters n)
    (χ : Option V → ∀ p : ℕ, DirichletCharacter ℂ p) (graph : Option V → Option V → ℤ)
    (unary : Option V → ℕ → ℂ) (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : graph (some a) (some a) = 0 ∧ graph (some b) (some b) = 0) (hreverse : graph (some b) (some a) = 0)
    (P : Finset ℕ) (Q : V → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (hprime : ∀ q ∈ Q a, q.Prime)
    (hnonprincipal : ∀ q ∈ Q a, χ (some a) q ^ graph (some a) (some b) ≠ 1)
    (A E : ℕ) (hA : 0 < A)
    (hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
    (hsmall : ∀ q ∈ Q a, ∀ s ∈ allFrequencyList n t, s.natAbs < q)
    (hsmall' : ∀ q ∈ Q a, ∀ s ∈ allFrequencyList n t', s.natAbs < q)
    (hlow : ∀ p ∈ Q b, 2 * A ≤ p) (hhigh : ∀ p ∈ Q b, p ≤ E)
    (lower : ℝ) (hlower : 0 < lower) (hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
    (Bq : ℕ) (hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
    (M : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : rangedWordTransferPairBound template template' D D' t t' hn hn' B f f' A E (Q b) (Q a) lower Bq ≤ δ ^ 2) :
    ‖∑ x : V → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      (finiteEdgeWeight (dirichletGraphEdge χ graph) unary (fixedPivotPrimeValues M (fun i => (x i : ℕ))) *
        (f.unitRangedCoefficient U D template t hn (expandedPrimeValues n (fun i => (fixedPivotPrimeValues M (fun j => (x j : ℕ)) i : ℤ))) *
          conj (f'.unitRangedCoefficient U' D' template' t' hn' (expandedPrimeValues n (fun i => (fixedPivotPrimeValues M (fun j => (x j : ℕ)) i : ℤ))))))‖ ≤ δ := by
  apply fixed_pivot_original_harmonic_pair_bound a b hab M P Q hQP (fun i => (hQmass i).ne')
    (fun x => finiteEdgeWeight (dirichletGraphEdge χ graph) unary x *
      (f.unitRangedCoefficient U D template t hn (expandedPrimeValues n (fun i => (x i : ℤ))) *
        conj (f'.unitRangedCoefficient U' D' template' t' hn' (expandedPrimeValues n (fun i => (x i : ℤ)))))) δ hδ
  intro outside
  have hs := selected_unit_ranged_expanded_word_pair_bound (some a) (some b) (fun h => hab (Option.some.inj h)) template template' U U' D D' t t' hn hn' B hB
    hwords hwords' hD hD' hU hU' hz hz' f f' χ graph unary hunary hself hreverse (Q b) (Q a) hprime
    hnonprincipal A E hA hMA hsmall hsmall' hlow hhigh lower hlower hlowerQ
    (hQmass b) (hQmass a) Bq hBq outside
  exact (sq_le_sq₀ (norm_nonneg _) hδ).mp (hs.trans hnum)

end Ostmann

end OAI
