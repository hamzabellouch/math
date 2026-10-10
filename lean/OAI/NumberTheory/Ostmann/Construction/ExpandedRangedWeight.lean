import OAI.NumberTheory.Ostmann.Construction.ExpandedRangeReplay
import OAI.NumberTheory.Ostmann.Construction.GroupedScheduleCoefficient

namespace OAI

/-! # The original all-stage ranges in the concrete Fourier coefficient -/

namespace Ostmann

open scoped Classical SchwartzMap FourierTransform ComplexConjugate

theorem expanded_schedule_ranged_weight_eq {I α : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (n : ℕ) → List (ScheduleAtomRange role n)) (F : ℕ → ℤ → ℂ)
    (depth n : ℕ) (hn : n ≤ depth) (path : List Bool)
    (current : CopyScheduleAtoms role n → List (ExpandedScheduledVariable α depth))
    (hc : ∀ i v, v ∈ current i → ExpandedCoordinateAfter n v)
    (x : ExpandedScheduledVariable α depth → ℕ) (t : FrequencyTree ℤ n) :
    (expandedScheduleRanges role (expandedPivotAddress α depth) ranges n path current).weight
      (fun τ v => F (wordTransferLeafValue τ) v)
      (expandedScheduledTemplate role (expandedPivotAddress α depth) childBound pivotBound n path current) x t =
      (if scheduleAtomRangesValid role childBound pivotBound ranges n (expandedAtomValues role n current x) t
        then 1 else 0) *
      recursiveTransferWeight (scheduleAtomSystem role childBound pivotBound)
        (fun τ v => F (scheduleAtomTotal role τ) v) (fun _ _ _ _ => 1) n
        ⟨n, expandedAtomValues role n current x⟩ t := by
  rw [WordRangeDecoration.weight_eq,
    expanded_schedule_weight_eq role childBound pivotBound F depth n hn path current hc x t]
  have he := expandedScheduleRanges_valid_iff role childBound pivotBound ranges depth n hn path current hc x t
  simp only [he]

noncomputable def expandedRootRanges {I V : Type*}
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j)) :
    WordRangeDecoration (ExpandedScheduledVariable V n) n :=
  expandedScheduleRanges role (expandedPivotAddress V n) ranges n [] (fun i => (words i).map Sum.inl)

noncomputable def groupedRangedFourierWeight {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t : FrequencyTree ℤ n) (x : V → ℕ) : ℂ :=
  (if scheduleAtomRangesValid role childBound pivotBound ranges n (fun i => ((words i).map x).prod) t
    then 1 else 0) * groupedScheduleFourierWeight role n words childBound pivotBound ψ X lo hi t x

/-- The actual grouped-atom weight with all intermediate product and word
bins is the coefficient used by the ranged one-sided bound. -/
theorem groupedRangedFourierWeight_coefficient {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : V → ℕ) :
    groupedRangedFourierWeight role n words childBound pivotBound ranges ψ X lo hi t x =
      (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi).rangedCoefficient
        (expandedRootRanges role n words ranges) (expandedRootTemplate role n words childBound pivotBound)
        t ht (expandedPrimeValues n (fun i => (x i : ℤ))) := by
  let F : ℕ → ℤ → ℂ := fun M v => (if (M : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
    normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((M : ℝ) / X)
  have he := expanded_schedule_ranged_weight_eq role childBound pivotBound ranges F n n le_rfl []
    (fun i => (words i).map Sum.inl) (expandedRootCoordinates_after role n words)
    (expandedPrimeNatValues n x) t
  have hx : expandedAtomValues role n (fun i => (words i).map Sum.inl) (expandedPrimeNatValues n x) =
      fun i => ((words i).map x).prod := by
    funext i
    unfold expandedAtomValues
    rw [List.map_map]
    rfl
  rw [hx] at he
  have hw := (expandedRootRanges role n words ranges).weight_coefficient
    (expandedRootTemplate role n words childBound pivotBound) (expandedPrimeNatValues n x)
    t ht ψ hreal X lo hi hlo hhi
  rw [expandedPrimeNatValues_cast] at hw
  exact he.symm.trans hw

end Ostmann

end OAI
