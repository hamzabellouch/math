import OAI.NumberTheory.Ostmann.Construction.FixedPivotPrimeOriginal
import OAI.NumberTheory.Ostmann.Construction.FixedPivotTopSupport

namespace OAI

/-! # Original-prior cancellation retaining all top prime tests -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical SchwartzMap

theorem fixed_pivot_full_original_pair_bound {J : Type*} [Fintype J] {K : Type*} [Fintype K] [Nonempty K] {n : ℕ}
    (a b : K) (hab : a ≠ b)
    (template template' : WordTransferTemplate (ExpandedScheduledVariable (Option (K)) n) n)
    (C C' : WordPrimeDecoration (Option (K)) n)
    (U U' D D' : WordRangeDecoration (ExpandedScheduledVariable (Option (K)) n) n)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (hC : C.Coordinates (· ≠ none)) (hC' : C'.Coordinates (· ≠ none))
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hwords' : template'.WordsBounded B)
    (hD : D.WordsBounded B) (hD' : D'.WordsBounded B)
    (hU : U.WordsBounded B) (hU' : U'.WordsBounded B)
    (f f' : WordFourierParameters n)
    (χ : Option (K) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (graph : Option (K) → Option (K) → ℤ)
    (unary : Option (K) → ℕ → ℂ) (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : graph (some a) (some a) = 0 ∧ graph (some b) (some b) = 0) (hreverse : graph (some b) (some a) = 0)
    (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (Q : K → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (hnonprincipal : ∀ q ∈ Q a, χ (some a) q ^ graph (some a) (some b) ≠ 1)
    (A E : ℕ) (hA : 0 < A)
    (hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
    (hsmall : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < p)
    (hsmall' : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < p)
    (hlow : ∀ p ∈ Q b, 2 * A ≤ p) (hhigh : ∀ p ∈ Q b, p ≤ E)
    (lower : ℝ) (hlower : 0 < lower) (hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
    (Bq : ℕ) (hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
    (α V R : ℝ) (hα : 0 ≤ α) (hV : 0 < V) (hR : 3 ≤ R)
    (M : ℕ) (hM : (M : ℝ) ≤ R)
    (hmax : ∀ i p, primeSubsetPrior P (Q i) p ≤ α)
    (hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
    (checks : J → TopPrimeCondition (K))
    (hchecks : ∀ j, (checks j).Bounded R)
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : rangedWordTransferPairBound template template' D D' t t' ht ht' B f f'
      A E (Q b) (Q a) lower Bq ≤ δ ^ 2) :
    ‖∑ x : K → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      (if ∀ j, (checks j).Holds (fun i => (x i : ℕ)) then
        finiteEdgeWeight (dirichletGraphEdge χ graph) unary (fixedPivotPrimeValues M (fun i => (x i : ℕ))) *
        (f.primeUnitRangedCoefficient C U D template t ht (fixedPivotPrimeValues M (fun i => (x i : ℕ))) *
          conj (f'.primeUnitRangedCoefficient C' U' D' template' t' ht' (fixedPivotPrimeValues M (fun i => (x i : ℕ))))) else 0)‖ ≤
      δ + ((SchwartzMap.seminorm ℝ 0 0 f.profile) ^ (2 ^ n) *
        (SchwartzMap.seminorm ℝ 0 0 f'.profile) ^ (2 ^ n)) *
        (((C.count + C'.count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) + Fintype.card J) *
        (α + Real.log R / V * α) := by
  let : Nonempty P := hP.to_subtype
  let N := (SchwartzMap.seminorm ℝ 0 0 f.profile) ^ (2 ^ n) *
    (SchwartzMap.seminorm ℝ 0 0 f'.profile) ^ (2 ^ n)
  let cost := ((C.count + C'.count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ)
  let atom := α + Real.log R / V * α
  have hatom : 0 ≤ atom := by
    dsimp [atom]
    have hr : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
    positivity
  have hN : 0 ≤ N := by
    dsimp [N]
    exact mul_nonneg (pow_nonneg (apply_nonneg _ _) _) (pow_nonneg (apply_nonneg _ _) _)
  have hbase := fixed_pivot_prime_original_pair_bound a b hab template template'
    C C' U U' D D' t t' ht ht' hC hC' B hB hwords hwords' hD hD' hU hU' f f'
    χ graph unary hunary hself hreverse P hP hprime Q hQP hQmass hnonprincipal
    A E hA hMA hsmall hsmall' hlow hhigh lower hlower hlowerQ Bq hBq
    α V R hα hV hR M hM hmax hlowerP hupperP hfreq hfreq' δ hδ hnum
  have hh := fixed_pivot_top_prime_coefficient_pair_bound (fun p : P => (p : ℕ)) Subtype.val_injective
    (fun p => hprime p p.property) checks C C' U U' D D' template template' t t' ht ht'
    f f' (fun i => primeSubsetPrior P (Q i))
    (fun i p => primeSubsetPrior_nonneg P (Q i) p)
    (fun i => primeSubsetPrior_mass P (Q i) (hQP i) (hQmass i).ne')
    α V R hα hV hR hmax (fun p => hlowerP p p.property)
    (fun p => hupperP p p.property) hchecks M
    (finiteEdgeWeight (dirichletGraphEdge χ graph) unary)
    (fun x => finiteEdgeWeight_norm _ _ x (dirichletGraphEdge_norm χ graph) hunary)
    (δ + N * cost * atom) (add_nonneg hδ (mul_nonneg (mul_nonneg hN (by positivity)) hatom))
    (by
      simp only [finiteProductPrior]
      convert hbase using 1
      dsimp [N, cost, atom]
      ring)
  change _ ≤ δ + N * (cost + Fintype.card J) * atom
  simp only [finiteProductPrior] at hh
  convert hh using 1
  dsimp [N, cost, atom]
  ring

end Ostmann

end OAI
