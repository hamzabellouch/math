import OAI.NumberTheory.Ostmann.Construction.ConstituentPairRatio
import OAI.NumberTheory.Ostmann.Construction.FiniteMatchedWindow

namespace OAI

/-! # The matched correlation under both original harmonic priors -/

namespace Ostmann
open scoped BigOperators ComplexConjugate Classical SchwartzMap FourierTransform

section
variable {I : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
variable (χ : ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
variable (e : Equiv.Perm (CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
variable (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
variable (hu : ∀ j ≤ n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b)

include hreal hu hκ in
theorem constituent_original_pair_bound
    (a b : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))) (hab : a ≠ b)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (B : ℕ) (hB : 1 ≤ B) (hwords : ((expandedRootTemplate role n (insertedConstituentWord role size n) childBound pivotBound)).WordsBounded B) (hwordsR : ((expandedRootTemplate role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) childBound pivotBound)).WordsBounded B)
    (hD : ((expandedRootRanges role n (insertedConstituentWord role size n) ranges)).WordsBounded B) (hD' : ((expandedRootRanges role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) ranges)).WordsBounded B)
    (hU : ((expandedRootRanges role n (insertedConstituentWord role size n) (totalAtomUnitRanges role))).WordsBounded B) (hU' : ((expandedRootRanges role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) (totalAtomUnitRanges role))).WordsBounded B)
    (hself : ((constituentMatchedGraph role size pivot n e)) a a = 0 ∧ ((constituentMatchedGraph role size pivot n e)) b b = 0) (hreverse : ((constituentMatchedGraph role size pivot n e)) b a = 0)
    (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (Q : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (hnonprincipal : ∀ q ∈ Q a, χ q ^ ((constituentMatchedGraph role size pivot n e)) a b ≠ 1)
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
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (hword : Fintype.card (CopyScheduleH (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n) + 1 ≤ B)
    (Z : ℝ) (hZ : 0 < Z)
    (loH : (CopyScheduleH (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n) → ℝ) (hloH : ∀ h, 0 ≤ loH h)
    (hcell : ∀ h p, p ∈ Q (.inl h) → loH h ≤ (p : ℝ))
    (hscale : Z ≤ ∏ h, loH h)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : rangedWordTransferPairBound (expandedRootTemplate role n (insertedConstituentWord role size n) childBound pivotBound) (expandedRootTemplate role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) childBound pivotBound) (((expandedRootRanges role n (insertedConstituentWord role size n) ranges)).prependRoot (originalProductRange ((retainedHWord (CopyScheduleH (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n) (CopyScheduleY (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n)).map some) n Z 0)) (expandedRootRanges role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) ranges) t t' ht ht' B (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi) (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi)
      A E (Q b) (Q a) lower Bq ≤ δ ^ 2) :
    let leaf := fun τ (v : ℤ) => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
      normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)
    let core := fun x : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) → P => constituentCharacterCore role size (fun _ => χ) κ pivot n P hprime
      childBound pivotBound ranges leaf (fun z : FrequencyTree ℤ n => z) (fun y => x (.inr y)) M
    ‖∑ x : (CopyScheduleH (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n) ⊕ (CopyScheduleY (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n) → P,
      ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      ((∏ h, primeSubsetPrior P (Q (.inl h)) (x (.inl (e h))) : ℝ) : ℂ) *
      (core x ((fun h => x (.inl h)), t) * conj (core x ((fun h => x (.inl (e h))), t')))‖ ≤
      (∏ h : (CopyScheduleH (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n), (∑ p ∈ Q (.inl h), (p : ℝ)⁻¹)⁻¹) * Z⁻¹ *
      (δ + ((SchwartzMap.seminorm ℝ 0 0 ((WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi)).profile) ^ (2 ^ n) *
        (SchwartzMap.seminorm ℝ 0 0 ((WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi)).profile) ^ (2 ^ n)) *
        (((((expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl ((insertedConstituentWord role size n) i)))).count + ((expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) i)))).count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) +
          (constituentPrimePairChecks ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) ++ atomPairChecks (insertedConstituentWord role size n) ++ atomPairChecks ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i)))).length) *
        (α + Real.log R / V * α)) := by
  extract_lets leaf core
  refine Eq.trans_le (congrArg norm (finite_enumeration_sum _ _ _))
    (finite_matched_window_bound P Q e
    (fun x => core x ((fun h => x (.inl h)), t) *
      conj (core x ((fun h => x (.inl (e h))), t'))) loH hloH hcell Z hZ hscale _ ?_)
  have hh := constituent_masked_pair_ratio_bound role size n χ κ pivot hκ e
    childBound pivotBound ranges ψ hreal X lo hi hlo hhi hu
    a b hab t t' ht ht' B hB hwords hwordsR hD hD' hU hU' hself hreverse
    P hP hprime Q hQP hQmass hnonprincipal A E hA hMA hsmall hsmall'
    hlow hhigh lower hlower hlowerQ Bq hBq α V R hα hV hR M hM hmax hlowerP hupperP
    hfreq hfreq' (retainedHWord (CopyScheduleH (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n) (CopyScheduleY (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n)) (by simpa only [retainedHWord_length] using hword) Z hZ δ hδ hnum
  dsimp only at hh
  simp only [retainedHWord_prod, Nat.cast_prod] at hh
  exact Eq.trans_le (congrArg norm (finite_enumeration_sum _ _ _)) hh

end
end Ostmann

end OAI
