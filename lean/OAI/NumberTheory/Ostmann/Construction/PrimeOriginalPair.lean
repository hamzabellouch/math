import OAI.NumberTheory.Ostmann.Construction.PrimeWordPairBound
import OAI.NumberTheory.Ostmann.Arithmetic.UnitRangedOriginalPair

namespace OAI

/-! # The complete two-history Y-coprimality estimate under harmonic priors -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical SchwartzMap

theorem finiteEdgeWeight_norm {I : Type*} [Fintype I]
    (E : I → I → ℕ → ℕ → ℂ) (ν : I → ℕ → ℂ) (x : I → ℕ)
    (hE : ∀ i j p q, ‖E i j p q‖ ≤ 1) (hν : ∀ i p, ‖ν i p‖ ≤ 1) :
    ‖finiteEdgeWeight E ν x‖ ≤ 1 := by
  unfold finiteEdgeWeight
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro i _
  rw [norm_mul, norm_prod]
  have hp : (∏ j, ‖E i j (x i) (x j)‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun j _ => hE i j _ _)
  exact (mul_le_mul (hν i _) hp (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    (by norm_num)).trans_eq (one_mul 1)

theorem prime_unit_ranged_original_pair_bound {m n : ℕ}
    (a b : Fin (m + 1)) (hab : a ≠ b)
    (template template' : WordTransferTemplate (ExpandedScheduledVariable (Fin (m + 1)) n) n)
    (C C' : WordPrimeDecoration (Fin (m + 1)) n)
    (U U' D D' : WordRangeDecoration (ExpandedScheduledVariable (Fin (m + 1)) n) n)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hwords' : template'.WordsBounded B)
    (hD : D.WordsBounded B) (hD' : D'.WordsBounded B)
    (hU : U.WordsBounded B) (hU' : U'.WordsBounded B)
    (f f' : WordFourierParameters n)
    (χ : Fin (m + 1) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (graph : Fin (m + 1) → Fin (m + 1) → ℤ)
    (unary : Fin (m + 1) → ℕ → ℂ) (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : graph a a = 0 ∧ graph b b = 0) (hreverse : graph b a = 0)
    (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (Q : Fin (m + 1) → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (hnonprincipal : ∀ q ∈ Q a, χ a q ^ graph a b ≠ 1)
    (A E : ℕ) (hA : 0 < A)
    (hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
    (hsmall : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < p)
    (hsmall' : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < p)
    (hlow : ∀ p ∈ Q b, 2 * A ≤ p) (hhigh : ∀ p ∈ Q b, p ≤ E)
    (lower : ℝ) (hlower : 0 < lower) (hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
    (Bq : ℕ) (hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
    (α V R : ℝ) (hα : 0 ≤ α) (hV : 0 < V) (hR : 3 ≤ R)
    (hmax : ∀ i p, primeSubsetPrior P (Q i) p ≤ α)
    (hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : rangedWordTransferPairBound template template' D D' t t' ht ht' B f f'
      A E (Q b) (Q a) lower Bq ≤ δ ^ 2) :
    ‖∑ x : Fin (m + 1) → P, ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      (finiteEdgeWeight (dirichletGraphEdge χ graph) unary (fun i => (x i : ℕ)) *
        (f.primeUnitRangedCoefficient C U D template t ht (fun i => (x i : ℕ)) *
          conj (f'.primeUnitRangedCoefficient C' U' D' template' t' ht' (fun i => (x i : ℕ)))))‖ ≤
      δ + ((SchwartzMap.seminorm ℝ 0 0 f.profile) ^ (2 ^ n) *
        (SchwartzMap.seminorm ℝ 0 0 f'.profile) ^ (2 ^ n)) *
        ((C.count + C'.count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) * (α + Real.log R / V * α) := by
  let : Nonempty P := hP.to_subtype
  obtain ⟨p₀, hp₀⟩ := hP
  have hz : ∀ s ∈ allFrequencyList n t, s ≠ 0 := by
    intro s hs
    exact Int.natAbs_pos.mp (hsmall p₀ hp₀ s hs).1
  have hz' : ∀ s ∈ allFrequencyList n t', s ≠ 0 := by
    intro s hs
    exact Int.natAbs_pos.mp (hsmall' p₀ hp₀ s hs).1
  have hbase := unit_ranged_expanded_word_pair_original_bound a b hab template template'
    U U' D D' t t' ht ht' B hB hwords hwords' hD hD' hU hU' hz hz' f f' χ graph unary hunary
    hself hreverse P Q hQP hQmass (fun q hq => hprime q (hQP a hq)) hnonprincipal
    A E hA hMA (fun q hq s hs => (hsmall q (hQP a hq) s hs).2)
    (fun q hq s hs => (hsmall' q (hQP a hq) s hs).2)
    hlow hhigh lower hlower hlowerQ Bq hBq δ hδ hnum
  exact prime_coefficient_pair_bound (fun p : P => (p : ℕ)) Subtype.val_injective
    (fun p => hprime p p.property) C C' U U' D D' template template' t t' ht ht'
    B hB hwords hwords' f f' (fun i => primeSubsetPrior P (Q i))
    (fun i p => primeSubsetPrior_nonneg P (Q i) p)
    (fun i => primeSubsetPrior_mass P (Q i) (hQP i) (hQmass i).ne')
    α α V R hα hα hV hR hmax hmax
    (fun p => hlowerP p p.property) (fun p => hupperP p p.property) hfreq hfreq'
    (fun p => hsmall p p.property) (fun p => hsmall' p p.property)
    (finiteEdgeWeight (dirichletGraphEdge χ graph) unary)
    (fun x => finiteEdgeWeight_norm _ _ x (dirichletGraphEdge_norm χ graph) hunary)
    δ hδ (by
      simp only [productPrior]
      convert hbase using 1
      congr 2
      ext x
      simp only [Finset.mem_univ])

end Ostmann

end OAI
