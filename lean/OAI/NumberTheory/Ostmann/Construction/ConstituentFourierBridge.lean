import OAI.NumberTheory.Ostmann.Construction.ConstituentWords
import OAI.NumberTheory.Ostmann.Construction.GroupedFullCoprime

namespace OAI

/-! # The actual prime constituents give the grouped full Fourier coefficient -/

namespace Ostmann

open scoped Classical SchwartzMap FourierTransform ComplexConjugate

theorem constituentExpandedTemplate_size {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (childBound pivotBound : ℕ → ℕ) (M : ℕ) (hM : 1 ≤ M) (hsize : ∀ i, size i ≤ M) :
    (expandedRootTemplate role n (scheduleConstituentWord role size n) childBound pivotBound).WordsBounded
      (2 * 3 ^ n * Fintype.card I * M + 4) := by
  apply expandedRootTemplate_size role n (scheduleConstituentWord role size n) childBound pivotBound M hM
  intro i
  rw [scheduleConstituentWord_length]
  exact hsize _

theorem constituent_top_checks {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (q : SurvivingConstituent role size n → ℕ)
    (hq : Pairwise (fun i j => (q i).Coprime (q j))) :
    ∀ c ∈ atomPairChecks (scheduleConstituentWord role size n), c.Holds q :=
  (atomPairChecks_iff (scheduleConstituentWord role size n) q).mpr
    (scheduleConstituentWord_pairwise role size n q hq)

/-- The top support of the original constituent assignment is exactly the
support used by the grouped Fourier development. No independent atom sample
or replacement distribution is introduced. -/
theorem constituent_full_weight_coefficient {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (q : SurvivingConstituent role size n → ℕ)
    (hq : Pairwise (fun i j => (q i).Coprime (q j)))
    (hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b) :
    groupedFullCoprimeFourierWeight role n (scheduleConstituentWord role size n)
      childBound pivotBound ranges ψ X lo hi t q =
    (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi).primeUnitRangedCoefficient
      (expandedSchedulePrimes role n n [] (fun i => (scheduleConstituentWord role size n i).map Sum.inl))
      (expandedRootRanges role n (scheduleConstituentWord role size n) (totalAtomUnitRanges role))
      (expandedRootRanges role n (scheduleConstituentWord role size n) ranges)
      (expandedRootTemplate role n (scheduleConstituentWord role size n) childBound pivotBound) t ht q := by
  rw [groupedFullCoprimeFourierWeight_coefficient role n (scheduleConstituentWord role size n)
    childBound pivotBound ranges ψ hreal X lo hi hlo hhi t ht q hu,
    ite_eq_left (constituent_top_checks role size n q hq)]

end Ostmann

end OAI
