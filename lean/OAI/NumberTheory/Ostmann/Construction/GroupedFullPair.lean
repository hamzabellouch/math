import OAI.NumberTheory.Ostmann.Construction.GroupedFullCoprime

namespace OAI

/-! # The exact original-prior pair with complete arithmetic support -/

namespace Ostmann

open scoped BigOperators Classical SchwartzMap FourierTransform ComplexConjugate

/-- Both histories and any external-integer tests use the same original
sample. No new distribution is assigned to reconstructed pivots. -/
theorem grouped_full_pair_mean {I V A : Type*} [Fintype I] [Fintype A]
    (role : I → CopyScheduleRole) (n : ℕ)
    (words words' : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (ht' : NonzeroInternalFrequencies n t')
    (hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b)
    (extra : List (TopPrimeCondition V)) (x : A → V → ℕ) (weight phase : A → ℂ) :
    (∑ a, weight a * (if ∀ c ∈ extra, c.Holds (x a) then
      phase a * (groupedFullCoprimeFourierWeight role n words childBound pivotBound ranges
        ψ X lo hi t (x a) *
        conj (groupedFullCoprimeFourierWeight role n words' childBound pivotBound ranges
          ψ X lo hi t' (x a))) else 0)) =
    ∑ a, weight a *
      (if ∀ c ∈ extra ++ atomPairChecks words ++ atomPairChecks words', c.Holds (x a) then
        phase a *
          ((WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi).primeUnitRangedCoefficient
            (expandedSchedulePrimes role n n [] (fun i => (words i).map Sum.inl))
            (expandedRootRanges role n words (totalAtomUnitRanges role))
            (expandedRootRanges role n words ranges) (expandedRootTemplate role n words childBound pivotBound)
            t ht (x a) *
          conj ((WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi).primeUnitRangedCoefficient
            (expandedSchedulePrimes role n n [] (fun i => (words' i).map Sum.inl))
            (expandedRootRanges role n words' (totalAtomUnitRanges role))
            (expandedRootRanges role n words' ranges) (expandedRootTemplate role n words' childBound pivotBound)
            t' ht' (x a))) else 0) := by
  apply Finset.sum_congr rfl
  intro a _
  rw [groupedFullCoprimeFourierWeight_coefficient role n words childBound pivotBound ranges
    ψ hreal X lo hi hlo hhi t ht (x a) hu,
    groupedFullCoprimeFourierWeight_coefficient role n words' childBound pivotBound ranges
    ψ hreal X lo hi hlo hhi t' ht' (x a) hu]
  simp only [List.mem_append, or_imp, forall_and]
  split_ifs <;> simp_all

end Ostmann

end OAI
