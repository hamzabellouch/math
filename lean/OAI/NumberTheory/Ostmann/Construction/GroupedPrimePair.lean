import OAI.NumberTheory.Ostmann.Construction.GroupedFixedPivotPair

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
theorem grouped_prime_original_pair_bound
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
    (hmax : ∀ i p, primeSubsetPrior P (Q i) p ≤ α)
    (hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
    (extra : List (TopPrimeCondition (Option K)))
    (hExtra : ∀ c ∈ extra, c.HasVariable) (hExtraR : ∀ c ∈ extra, c.Bounded R)
    (hLeft : ∀ c ∈ atomPairChecks words, c.HasVariable)
    (hRight : ∀ c ∈ atomPairChecks words', c.HasVariable)
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : rangedWordTransferPairBound TplL TplR ((DrL).prependRoot (originalProductRange ([] : List (Option K)) n 1 0)) DrR t t' ht ht' B FP FP
      A E (Q b) (Q a) lower Bq ≤ δ ^ 2) :
    let q := fun x : K → P => fixedPivotPrimeValues 1 (fun i => (x i : ℕ))
    let G : (K → P) → ℂ := fun x =>
      ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
        (if ∀ c ∈ extra, c.Holds (q x) then
          finiteEdgeWeight (dirichletGraphEdge χ graph) unary (fun i => (x i : ℕ)) *
            (groupedFullCoprimeFourierWeight role n words childBound pivotBound ranges ψ X lo hi t (q x) *
              conj (groupedFullCoprimeFourierWeight role n words' childBound pivotBound ranges ψ X lo hi t' (q x)))
        else 0)
    ‖∑ x, G x‖ ≤
      δ + ((SchwartzMap.seminorm ℝ 0 0 (FP).profile) ^ (2 ^ n) *
        (SchwartzMap.seminorm ℝ 0 0 (FP).profile) ^ (2 ^ n)) *
        ((((PrL).count + (PrR).count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) +
          (extra ++ atomPairChecks words ++ atomPairChecks words').length) *
        (α + Real.log R / V * α) := by
  have hh := grouped_fixed_pivot_original_ratio_bound role n words words'
    childBound pivotBound ranges ψ hreal X lo hi hlo hhi hu
    a b hab t t' ht ht' hC hC' B hB hwords hwords' hD hD' hU hU'
    χ graph unary hunary hself hreverse P hP hprime Q hQP hQmass hnonprincipal
    A E hA hMA hsmall hsmall' hlow hhigh lower hlower hlowerQ Bq hBq
    α V R hα hV hR 1 (by norm_num; linarith) hmax hlowerP hupperP
    extra hExtra hExtraR hLeft hRight hfreq hfreq' [] (by simpa using hB)
    1 (by norm_num) δ hδ hnum
  dsimp only at hh ⊢
  simpa only [List.map_nil, List.prod_nil, Nat.cast_one, div_one, le_refl,
    ite_true, Complex.ofReal_one, one_mul] using hh

end
end Ostmann

end OAI
