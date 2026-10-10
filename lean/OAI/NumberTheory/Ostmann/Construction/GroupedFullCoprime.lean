import OAI.NumberTheory.Ostmann.Construction.ScheduleFullCoprime
import OAI.NumberTheory.Ostmann.Construction.GroupedCoprimeCoefficient
import OAI.NumberTheory.Ostmann.Construction.AtomTopSupport

namespace OAI

/-! # The original complete coprimality support in the grouped Fourier weight -/

namespace Ostmann

open scoped Classical SchwartzMap FourierTransform ComplexConjugate

theorem groupedUnitRangedFourierWeight_support {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t : FrequencyTree ℤ n) (x : V → ℕ)
    (hn : groupedUnitRangedFourierWeight role n words childBound pivotBound ranges
      ψ X lo hi t x ≠ 0) :
    ValidTransferHistory (scheduleAtomSystem role childBound pivotBound) n
      ⟨n, fun i => ((words i).map x).prod⟩ t ∧
    scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n
      (fun i => ((words i).map x).prod) t := by
  unfold groupedUnitRangedFourierWeight at hn
  obtain ⟨hu, hr⟩ := mul_ne_zero_iff.mp hn
  have hu' : scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n
      (fun i => ((words i).map x).prod) t := by
    by_contra h
    simp only [h, ite_false, ne_eq, not_true_eq_false] at hu
  unfold groupedRangedFourierWeight at hr
  have hb := (mul_ne_zero_iff.mp hr).2
  exact ⟨recursiveTransferWeight_nonzero_valid _ _ _ _ _ _ hb, hu'⟩

noncomputable def groupedFullCoprimeFourierWeight {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t : FrequencyTree ℤ n) (x : V → ℕ) : ℂ :=
  (if scheduleAtomFullCoprimeValid role childBound pivotBound n
      (fun i => ((words i).map x).prod) t then 1 else 0) *
    groupedUnitRangedFourierWeight role n words childBound pivotBound ranges ψ X lo hi t x

theorem groupedFullCoprimeFourierWeight_reduced {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t : FrequencyTree ℤ n) (x : V → ℕ)
    (hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b) :
    groupedFullCoprimeFourierWeight role n words childBound pivotBound ranges ψ X lo hi t x =
      if Pairwise (fun i j => ((words i).map x).prod.Coprime ((words j).map x).prod) then
        groupedCoprimeFourierWeight role n words childBound pivotBound ranges ψ X lo hi t x
      else 0 := by
  by_cases hn : groupedUnitRangedFourierWeight role n words childBound pivotBound ranges
      ψ X lo hi t x = 0
  · simp only [groupedFullCoprimeFourierWeight, groupedCoprimeFourierWeight, hn, mul_zero, ite_self]
  · obtain ⟨hv, hunit⟩ := groupedUnitRangedFourierWeight_support role n words childBound
      pivotBound ranges ψ X lo hi t x hn
    have he := schedule_full_coprime_iff_reduced role childBound pivotBound n
      (fun i => ((words i).map x).prod) t hu hv hunit
    simp only [groupedFullCoprimeFourierWeight, groupedCoprimeFourierWeight, he]
    split_ifs <;> simp_all

/-- The original large-coprimality gates are represented exactly, even on
invalid histories, by the explicit top prime tests and reconstructed Y tests. -/
theorem groupedFullCoprimeFourierWeight_coefficient {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : V → ℕ)
    (hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b) :
    groupedFullCoprimeFourierWeight role n words childBound pivotBound ranges ψ X lo hi t x =
      if ∀ c ∈ atomPairChecks words, c.Holds x then
        (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi).primeUnitRangedCoefficient
          (expandedSchedulePrimes role n n [] (fun i => (words i).map Sum.inl))
          (expandedRootRanges role n words (totalAtomUnitRanges role))
          (expandedRootRanges role n words ranges) (expandedRootTemplate role n words childBound pivotBound)
          t ht x
      else 0 := by
  rw [groupedFullCoprimeFourierWeight_reduced role n words childBound pivotBound ranges
    ψ X lo hi t x hu, groupedCoprimeFourierWeight_coefficient role n words childBound
    pivotBound ranges ψ hreal X lo hi hlo hhi t ht x]
  simp only [atomPairChecks_iff]

end Ostmann

end OAI
