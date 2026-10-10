import OAI.NumberTheory.Ostmann.Construction.SchedulePairwiseReplay

namespace OAI

/-! # Recovering the complete large-coprimality support from the reduced tests -/

namespace Ostmann

open scoped BigOperators Classical

/-- The original requirements at every reversed transfer: current atoms are
pairwise coprime, and the inserted pivot is coprime to every current atom. -/
noncomputable def scheduleAtomFullCoprimeValid {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ) :
    (n : ℕ) → (CopyScheduleAtoms role n → ℕ) → FrequencyTree ℤ n → Prop
  | 0, x, _ => Pairwise (fun i j => (x i).Coprime (x j))
  | n + 1, x, t =>
      let P := historyPivot (scheduleAtomSystem role childBound pivotBound) ⟨n + 1, x⟩
        t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      Pairwise (fun i j => (x i).Coprime (x j)) ∧ (∀ i, P.Coprime (x i)) ∧
        scheduleAtomFullCoprimeValid role childBound pivotBound n
          (reverseCopyLabelMap role n true P x) t.2.1 ∧
        scheduleAtomFullCoprimeValid role childBound pivotBound n
          (reverseCopyLabelMap role n false P x) t.2.2

theorem schedule_full_coprime_reduced {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (h : scheduleAtomFullCoprimeValid role childBound pivotBound n x t) :
    Pairwise (fun i j => (x i).Coprime (x j)) ∧
      scheduleAtomCoprimalitiesValid role childBound pivotBound n x t := by
  induction n with
  | zero => exact ⟨h, trivial⟩
  | succ n ih =>
    exact ⟨h.1, (fun i => (h.2.1 _).symm), (ih _ _ h.2.2.1).2,
      (ih _ _ h.2.2.2).2⟩

/-- There is no loss of original support: all the omitted H tests follow
from the reconstruction equation and the retained frequency-unit tests. -/
theorem schedule_full_coprime_iff_reduced {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b)
    (hv : ValidTransferHistory (scheduleAtomSystem role childBound pivotBound) n ⟨n, x⟩ t)
    (hunits : scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n x t) :
    scheduleAtomFullCoprimeValid role childBound pivotBound n x t ↔
      Pairwise (fun i j => (x i).Coprime (x j)) ∧
        scheduleAtomCoprimalitiesValid role childBound pivotBound n x t := by
  constructor
  · exact schedule_full_coprime_reduced role childBound pivotBound n x t
  · rintro ⟨hpair, hY⟩
    have hall := schedule_pairwise_of_reduced_support role childBound pivotBound n x t
      hu hv hunits hY hpair
    clear hpair
    induction n with
    | zero => exact hall
    | succ n ih =>
      obtain ⟨P, hp, hvL, hvR⟩ := hv
      simp only [scheduleAtomUnitsValid, hp.historyPivot_eq] at hunits
      simp only [scheduleAtomCoprimalitiesValid, hp.historyPivot_eq] at hY
      simp only [scheduleAtomPairwiseValid, hp.historyPivot_eq] at hall
      simp only [scheduleAtomFullCoprimeValid, hp.historyPivot_eq]
      have hL := scheduleAtomUnitsValid_root role childBound pivotBound n
        (reverseCopyLabelMap role n true P x) t.2.1 hunits.2.1
      have hR := scheduleAtomUnitsValid_root role childBound pivotBound n
        (reverseCopyLabelMap role n false P x) t.2.2 hunits.2.2
      have hleft : (∏ i : CopyScheduleH role n, x ⟨.inl (true, i.val), i.property⟩).Coprime
          (frequencyRoot n t.2.1).natAbs := by
        apply Nat.coprime_fintype_prod_left_iff.mpr
        intro i
        simpa only [reverseCopyLabelMap_copied] using hL ⟨i.val, i.property.1⟩
      have hright : (∏ i : CopyScheduleH role n, x ⟨.inl (false, i.val), i.property⟩).Coprime
          (frequencyRoot n t.2.2).natAbs := by
        apply Nat.coprime_fintype_prod_left_iff.mpr
        intro i
        simpa only [reverseCopyLabelMap_copied] using hR ⟨i.val, i.property.1⟩
      have hP := schedule_pivot_coprime_all role n x P t.1
        (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) hall.1 hleft hright
        (by simpa only [scheduleAtomSystem, scheduleAtomLeft, scheduleAtomRight, Nat.cast_prod]
            using hp.relation)
        (fun i => (hY.1 i).symm)
      have hu' : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b :=
        fun j hj => hu j (by omega)
      exact ⟨hall.1, hP, ih _ _ hu' hvL hunits.2.1 hY.2.1 hall.2.1,
        ih _ _ hu' hvR hunits.2.2 hY.2.2 hall.2.2⟩

end Ostmann

end OAI
