import OAI.NumberTheory.Ostmann.Construction.ReverseCopyCoprime
import OAI.NumberTheory.Ostmann.Construction.ExpandedPrimeReplay
import OAI.NumberTheory.Ostmann.Arithmetic.TotalAtomUnits

namespace OAI

/-! # The reduced support implies every original pairwise-coprimality gate -/

namespace Ostmann

open scoped BigOperators Classical

theorem scheduleAtomUnitsValid_root {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hu : scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n x t) :
    ∀ i, (x i).Coprime (frequencyRoot n t).natAbs := by
  cases n with
  | zero => exact (totalAtomUnitRanges_iff role 0 x t).mp hu
  | succ n => exact (totalAtomUnitRanges_iff role (n + 1) x t.1).mp hu.1

noncomputable def scheduleAtomPairwiseValid {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ) :
    (n : ℕ) → (CopyScheduleAtoms role n → ℕ) → FrequencyTree ℤ n → Prop
  | 0, x, _ => Pairwise (fun i j => (x i).Coprime (x j))
  | n + 1, x, t =>
      let P := historyPivot (scheduleAtomSystem role childBound pivotBound) ⟨n + 1, x⟩
        t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      Pairwise (fun i j => (x i).Coprime (x j)) ∧
        scheduleAtomPairwiseValid role childBound pivotBound n
          (reverseCopyLabelMap role n true P x) t.2.1 ∧
        scheduleAtomPairwiseValid role childBound pivotBound n
          (reverseCopyLabelMap role n false P x) t.2.2

/-- All H-coprimalities are forced by the signed reconstruction and inherited
frequency-units. Only the Y checks and top pairwise support need be retained. -/
theorem schedule_pairwise_of_reduced_support {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b)
    (hv : ValidTransferHistory (scheduleAtomSystem role childBound pivotBound) n ⟨n, x⟩ t)
    (hunits : scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n x t)
    (hY : scheduleAtomCoprimalitiesValid role childBound pivotBound n x t)
    (hpair : Pairwise (fun i j => (x i).Coprime (x j))) :
    scheduleAtomPairwiseValid role childBound pivotBound n x t := by
  induction n with
  | zero => exact hpair
  | succ n ih =>
    obtain ⟨P, hp, hvL, hvR⟩ := hv
    simp only [scheduleAtomUnitsValid, hp.historyPivot_eq] at hunits
    simp only [scheduleAtomCoprimalitiesValid, hp.historyPivot_eq] at hY
    simp only [scheduleAtomPairwiseValid, hp.historyPivot_eq]
    have hL := scheduleAtomUnitsValid_root role childBound pivotBound n
      (reverseCopyLabelMap role n true P x) t.2.1 hunits.2.1
    have hR := scheduleAtomUnitsValid_root role childBound pivotBound n
      (reverseCopyLabelMap role n false P x) t.2.2 hunits.2.2
    have hleft : (∏ i : CopyScheduleH role n, x ⟨.inl (true, i.val), i.property⟩).Coprime
        (frequencyRoot n t.2.1).natAbs := by
      apply Nat.coprime_fintype_prod_left_iff.mpr
      intro i
      have hh := hL ⟨i.val, i.property.1⟩
      rw [reverseCopyLabelMap_copied] at hh
      exact hh
    have hright : (∏ i : CopyScheduleH role n, x ⟨.inl (false, i.val), i.property⟩).Coprime
        (frequencyRoot n t.2.2).natAbs := by
      apply Nat.coprime_fintype_prod_left_iff.mpr
      intro i
      have hh := hR ⟨i.val, i.property.1⟩
      rw [reverseCopyLabelMap_copied] at hh
      exact hh
    have hP := schedule_pivot_coprime_all role n x P t.1
      (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) hpair hleft hright
      (by simpa only [scheduleAtomSystem, scheduleAtomLeft, scheduleAtomRight, Nat.cast_prod] using hp.relation)
      (fun i => (hY.1 i).symm)
    have hu' : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b :=
      fun j hj => hu j (by omega)
    refine ⟨hpair, ?_, ?_⟩
    · exact ih _ t.2.1 hu' hvL hunits.2.1 hY.2.1
        (reverseCopyLabelMap_pairwise_coprime role n true P x (hu n (by omega)) hpair hP)
    · exact ih _ t.2.2 hu' hvR hunits.2.2 hY.2.2
        (reverseCopyLabelMap_pairwise_coprime role n false P x (hu n (by omega)) hpair hP)

end Ostmann

end OAI
