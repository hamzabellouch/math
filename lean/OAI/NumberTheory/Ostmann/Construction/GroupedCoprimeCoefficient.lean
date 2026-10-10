import OAI.NumberTheory.Ostmann.Construction.PrimeWordCoefficient
import OAI.NumberTheory.Ostmann.Construction.ExpandedPrimeCount
import OAI.NumberTheory.Ostmann.Construction.GroupedUnitCoefficient

namespace OAI

/-! # The reconstructed Y-coprimalities in the original grouped Fourier weight -/

namespace Ostmann

open scoped Classical SchwartzMap FourierTransform ComplexConjugate

noncomputable def groupedCoprimeFourierWeight {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t : FrequencyTree ℤ n) (x : V → ℕ) : ℂ :=
  (if scheduleAtomCoprimalitiesValid role childBound pivotBound n
      (fun i => ((words i).map x).prod) t then 1 else 0) *
    groupedUnitRangedFourierWeight role n words childBound pivotBound ranges ψ X lo hi t x

theorem groupedCoprimeFourierWeight_coefficient {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : V → ℕ) :
    groupedCoprimeFourierWeight role n words childBound pivotBound ranges ψ X lo hi t x =
      (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi).primeUnitRangedCoefficient
        (expandedSchedulePrimes role n n [] (fun i => (words i).map Sum.inl))
        (expandedRootRanges role n words (totalAtomUnitRanges role))
        (expandedRootRanges role n words ranges) (expandedRootTemplate role n words childBound pivotBound)
        t ht x := by
  let p := WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi
  rw [p.primeUnitRangedCoefficient_nat]
  have he := expandedSchedulePrimes_valid_iff role childBound pivotBound n n le_rfl []
    (fun i => (words i).map Sum.inl) (expandedRootCoordinates_after role n words)
    (expandedRoot_actual_coordinates role n words) (expandedPrimeNatValues n x) x (fun _ => rfl) t
  have hx : expandedAtomValues role n (fun i => (words i).map Sum.inl) (expandedPrimeNatValues n x) =
      fun i => ((words i).map x).prod := by
    funext i
    unfold expandedAtomValues
    rw [List.map_map]
    rfl
  rw [hx] at he
  unfold groupedCoprimeFourierWeight
  rw [groupedUnitRangedFourierWeight_coefficient role n words childBound pivotBound ranges
    ψ hreal X lo hi hlo hhi t ht x]
  congr 1
  simp only [expandedRootTemplate, he]

end Ostmann

end OAI
