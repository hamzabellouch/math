import OAI.NumberTheory.Ostmann.Construction.RetainedGraphRatioPair
import OAI.NumberTheory.Ostmann.Construction.GroupedFullPair
import OAI.NumberTheory.Ostmann.Construction.FixedPivotTopConditions

namespace OAI

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical SchwartzMap FourierTransform

section
variable {I K : Type*} [Fintype I] [Fintype K] [Nonempty K]
variable (role : I → CopyScheduleRole) (n : ℕ)
variable (words words' : CopyScheduleAtoms role n → List (Option K))
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
variable (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
variable (hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b)

local notation "TplL" => expandedRootTemplate role n words childBound pivotBound
local notation "TplR" => expandedRootTemplate role n words' childBound pivotBound
local notation "PrL" => expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (words i))
local notation "PrR" => expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (words' i))
local notation "UrL" => expandedRootRanges role n words (totalAtomUnitRanges role)
local notation "UrR" => expandedRootRanges role n words' (totalAtomUnitRanges role)
local notation "DrL" => expandedRootRanges role n words ranges
local notation "DrR" => expandedRootRanges role n words' ranges
local notation "FP" => WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi

include hreal hu in
theorem grouped_fixed_pivot_original_ratio_bound
    (a b : K) (hab : a ≠ b)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (hC : (PrL).Coordinates (· ≠ none)) (hC' : (PrR).Coordinates (· ≠ none))
    (B : ℕ) (hB : 1 ≤ B) (hwords : (TplL).WordsBounded B) (hwords' : (TplR).WordsBounded B)
    (hD : (DrL).WordsBounded B) (hD' : (DrR).WordsBounded B)
    (hU : (UrL).WordsBounded B) (hU' : (UrR).WordsBounded B)
    (χ : K → ∀ p : ℕ, DirichletCharacter ℂ p)
    (graph : K → K → ℤ)
    (unary : K → ℕ → ℂ) (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : graph a a = 0 ∧ graph b b = 0) (hreverse : graph b a = 0)
    (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (Q : K → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
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
    (M : ℕ) (hM : (M : ℝ) ≤ R)
    (hmax : ∀ i p, primeSubsetPrior P (Q i) p ≤ α)
    (hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
    (extra : List (TopPrimeCondition (Option K)))
    (hExtra : ∀ c ∈ extra, c.HasVariable) (hExtraR : ∀ c ∈ extra, c.Bounded R)
    (hLeft : ∀ c ∈ atomPairChecks words, c.HasVariable)
    (hRight : ∀ c ∈ atomPairChecks words', c.HasVariable)
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (word : List (K)) (hword : word.length + 1 ≤ B)
    (Z : ℝ) (hZ : 0 < Z)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : rangedWordTransferPairBound TplL TplR ((DrL).prependRoot (originalProductRange (word.map some) n Z 0)) DrR t t' ht ht' B FP FP
      A E (Q b) (Q a) lower Bq ≤ δ ^ 2) :
    let q := fun x : K → P => fixedPivotPrimeValues M (fun i => (x i : ℕ))
    let G : (K → P) → ℂ := fun x =>
      ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
        (if ∀ c ∈ extra, c.Holds (q x) then
          finiteEdgeWeight (dirichletGraphEdge χ graph) unary (fun i => (x i : ℕ)) *
            (groupedFullCoprimeFourierWeight role n words childBound pivotBound ranges ψ X lo hi t (q x) *
              conj (groupedFullCoprimeFourierWeight role n words' childBound pivotBound ranges ψ X lo hi t' (q x)))
        else 0)
    ‖∑ x, ((Z / ((word.map (fun i => (x i : ℕ))).prod : ℝ) : ℝ) : ℂ) *
      (if Z ≤ ((word.map (fun i => (x i : ℕ))).prod : ℝ) then G x else 0)‖ ≤
      δ + ((SchwartzMap.seminorm ℝ 0 0 (FP).profile) ^ (2 ^ n) *
        (SchwartzMap.seminorm ℝ 0 0 (FP).profile) ^ (2 ^ n)) *
        ((((PrL).count + (PrR).count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) +
          (extra ++ atomPairChecks words ++ atomPairChecks words').length) *
        (α + Real.log R / V * α) := by
  let tests := extra ++ atomPairChecks words ++ atomPairChecks words'
  have htests : ∀ c ∈ tests, c.HasVariable := by
    simpa only [tests, List.forall_mem_append] using ⟨⟨hExtra, hLeft⟩, hRight⟩
  have htestsR : ∀ c ∈ tests, c.Bounded R := by
    simpa only [tests, List.forall_mem_append] using
      ⟨⟨hExtraR, atomPairChecks_bounded words R⟩, atomPairChecks_bounded words' R⟩
  have hh := retained_graph_original_pair_ratio_bound a b hab TplL TplR PrL PrR UrL UrR DrL DrR
    t t' ht ht' hC hC' B hB hwords hwords' hD hD' hU hU' FP FP
    χ graph unary hunary hself hreverse P hP hprime Q hQP hQmass hnonprincipal
    A E hA hMA hsmall hsmall' hlow hhigh lower hlower hlowerQ Bq hBq
    α V R hα hV hR M hM hmax hlowerP hupperP
    (fixedPivotCheckAt M tests htests) (fixedPivotCheckAt_bounded M R hM tests htests htestsR)
    hfreq hfreq' word hword Z hZ δ hδ hnum
  dsimp only at hh ⊢
  rw [Fintype.card_fin] at hh
  simp_rw [fixedPivotCheckAt_all] at hh
  convert hh using 1
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [groupedFullCoprimeFourierWeight_coefficient role n words childBound pivotBound ranges
    ψ hreal X lo hi hlo hhi t ht _ hu,
    groupedFullCoprimeFourierWeight_coefficient role n words' childBound pivotBound ranges
      ψ hreal X lo hi hlo hhi t' ht' _ hu]
  simp only [tests, List.mem_append, or_imp, forall_and]
  split_ifs <;> simp_all

end
end Ostmann

end OAI
