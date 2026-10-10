import OAI.NumberTheory.Ostmann.Construction.ConstituentFinalPair
import OAI.NumberTheory.Ostmann.Construction.PrimeWordEmbedding
import OAI.NumberTheory.Ostmann.Construction.ConstituentPairFactors

namespace OAI

/-! # One-sided cancellation for the actual final fixed-history pair -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

section
variable {I : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
variable (e : Equiv.Perm (SurvivingConstituent role size n))
variable (hχ : ∀ i, χ (copyScheduleOrigin n (e i).val) = χ (copyScheduleOrigin n i.val))
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
variable (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
variable (hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b)
local notation "K" => SurvivingConstituent role size n
local notation "ρ" => (fun i : Σ a, Fin (size a) => role (Sigma.fst i))
local notation "W" => primeWordEmbedding (scheduleConstituentWord role size n)
local notation "W'" => primeWordEmbedding (fun v => List.map e (scheduleConstituentWord role size n v))
local notation "G" => graphDifference (scheduledSurvivorGraph ρ pivot n)
  (transportGraph e (scheduledSurvivorGraph ρ pivot n))
local notation "Tpl" => expandedRootTemplate role n W childBound pivotBound
local notation "Tpl'" => expandedRootTemplate role n W' childBound pivotBound
local notation "D" => expandedRootRanges role n W ranges
local notation "D'" => expandedRootRanges role n W' ranges
local notation "U" => expandedRootRanges role n W (totalAtomUnitRanges role)
local notation "U'" => expandedRootRanges role n W' (totalAtomUnitRanges role)
local notation "Pr" => expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (W i))
local notation "Pr'" => expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (W' i))
local notation "FP" => WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi

include hκ hχ hreal hu in
theorem constituent_final_pair_bound
    (a b : K) (hab : a ≠ b)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (ht' : NonzeroInternalFrequencies n t') (hroot : frequencyRoot n t = frequencyRoot n t')
    (B : ℕ) (hB : 1 ≤ B) (hwords : (Tpl).WordsBounded B) (hwords' : (Tpl').WordsBounded B)
    (hD : (D).WordsBounded B) (hD' : (D').WordsBounded B)
    (hU : (U).WordsBounded B) (hU' : (U').WordsBounded B) (hreverse : G b a = 0)
    (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (Q : K → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (hnonprincipal : ∀ q ∈ Q a, χ (copyScheduleOrigin n a.val) q ^ G a b ≠ 1)
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
    (hnum : rangedWordTransferPairBound Tpl Tpl'
      ((D).prependRoot (originalProductRange ([] : List (Option K)) n 1 0)) D' t t' ht ht' B FP FP
      A E (Q b) (Q a) lower Bq ≤ δ ^ 2)
    (center : ∀ p : ℕ, ZMod p) :
    ‖∑ q : K → P, ((∏ i, primeSubsetPrior P (Q i) (q i) : ℝ) : ℂ) *
      (constituentPrimeTerm role size χ κ pivot n P hprime childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center t q *
      conj (constituentPrimeTerm role size χ κ pivot n P hprime childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center t' (fun i => q (e i))))‖ ≤
    δ + ((SchwartzMap.seminorm ℝ 0 0 (FP).profile) ^ (2 ^ n) *
      (SchwartzMap.seminorm ℝ 0 0 (FP).profile) ^ (2 ^ n)) *
      ((((Pr).count + (Pr').count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) +
        (constituentPrimePairChecks K ++ atomPairChecks W ++ atomPairChecks W').length) *
      (α + Real.log R / V * α) := by
  let : Nonempty K := ⟨a⟩
  have hself (i : K) : G i i = 0 := by
    simp only [graphDifference, transportGraph, scheduledSurvivorGraph,
      copyScheduleGraph_diagonal initialCompleteGraph pivot initialCompleteGraph_self, sub_self]
  have hn (i : K) (p : ℕ) :
      ‖scheduledSurvivorUnary ρ χ κ pivot n t i p *
        conj (scheduledSurvivorUnary ρ χ κ pivot n t' (e.symm i) p)‖ ≤ 1 := by
    apply graphQuotientUnary_norm
    · intro j q
      exact copyScheduleUnary_norm_le_one χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        (initialRegularUnary_norm_le_one χ κ hκ) n t j.val q
    · intro j q
      exact copyScheduleUnary_norm_le_one χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        (initialRegularUnary_norm_le_one χ κ hκ) n t' (e.symm j).val q
  have hh := grouped_prime_original_pair_bound role n W W' childBound pivotBound ranges
    ψ hreal X lo hi hlo hhi hu a b hab t t' ht ht'
    (primeWordEmbedding_unfixed role n _) (primeWordEmbedding_unfixed role n _)
    B hB hwords hwords' hD hD' hU hU'
    (fun i => χ (copyScheduleOrigin n i.val)) G
    (fun i p => scheduledSurvivorUnary ρ χ κ pivot n t i p *
      conj (scheduledSurvivorUnary ρ χ κ pivot n t' (e.symm i) p)) hn
    ⟨hself a, hself b⟩ hreverse P hP hprime Q hQP hQmass hnonprincipal
    A E hA hMA hsmall hsmall' hlow hhigh lower hlower hlowerQ Bq hBq
    α V R hα hV hR hmax hlowerP hupperP
    (constituentPrimePairChecks K) (constituentPrimePairChecks_hasVariable K)
    (atomPairChecks_bounded _ R) (primeWordEmbedding_hasVariable _) (primeWordEmbedding_hasVariable _)
    hfreq hfreq' δ hδ hnum
  dsimp only at hh
  simp_rw [constituentPrimePairChecks_iff,
    groupedFullCoprimeFourierWeight_primeWordEmbedding] at hh
  apply Eq.trans_le (congrArg norm ?_) hh
  apply Finset.sum_congr (by ext q; simp only [Finset.mem_univ])
  intro q _
  congr 1
  exact constituentPrimeTerm_pair role size χ κ pivot n P hprime childBound pivotBound ranges
    ψ X lo hi t t' hroot e hχ q center

end
end Ostmann

end OAI
