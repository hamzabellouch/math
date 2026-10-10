import OAI.NumberTheory.Ostmann.Arithmetic.TotalAtomUnits
import OAI.NumberTheory.Ostmann.Arithmetic.UnitRangedOriginalPair

namespace OAI

/-! # The original all-atom frequency-units in the ranged Fourier weight -/

namespace Ostmann

open scoped Classical SchwartzMap FourierTransform ComplexConjugate

noncomputable def groupedUnitRangedFourierWeight {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t : FrequencyTree ℤ n) (x : V → ℕ) : ℂ :=
  (if scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n
      (fun i => ((words i).map x).prod) t then 1 else 0) *
    groupedRangedFourierWeight role n words childBound pivotBound ranges ψ X lo hi t x

/-- Each actual atom is a unit modulo the frequency of every state in which
it occurs. These conditions remain inside the exact polynomial coefficient. -/
theorem groupedUnitRangedFourierWeight_coefficient {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : V → ℕ) :
    groupedUnitRangedFourierWeight role n words childBound pivotBound ranges ψ X lo hi t x =
      (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi).unitRangedCoefficient
        (expandedRootRanges role n words (totalAtomUnitRanges role))
        (expandedRootRanges role n words ranges) (expandedRootTemplate role n words childBound pivotBound)
        t ht (expandedPrimeValues n (fun i => (x i : ℤ))) := by
  let p := WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi
  have he := p.unitRangedCoefficient_nat_all
    (expandedRootRanges role n words (totalAtomUnitRanges role)) (expandedRootRanges role n words ranges)
    (expandedRootTemplate role n words childBound pivotBound) t ht (expandedPrimeNatValues n x)
  rw [expandedPrimeNatValues_cast] at he
  have hunit := expandedScheduleUnits_valid_iff role childBound pivotBound (totalAtomUnitRanges role)
    n n le_rfl [] (fun i => (words i).map Sum.inl) (expandedRootCoordinates_after role n words)
    (expandedPrimeNatValues n x) t
  have hx : expandedAtomValues role n (fun i => (words i).map Sum.inl) (expandedPrimeNatValues n x) =
      fun i => ((words i).map x).prod := by
    funext i
    unfold expandedAtomValues
    rw [List.map_map]
    rfl
  rw [hx] at hunit
  have hbase := groupedRangedFourierWeight_coefficient role n words childBound pivotBound ranges
    ψ hreal X lo hi hlo hhi t ht x
  rw [he, ← hbase]
  unfold groupedUnitRangedFourierWeight
  congr 1
  simp only [expandedRootRanges, expandedRootTemplate, hunit]

end Ostmann

end OAI
