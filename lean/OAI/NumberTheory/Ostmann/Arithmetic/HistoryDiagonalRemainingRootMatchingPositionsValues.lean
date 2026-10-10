import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatchingPositions

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatching
open Construction

theorem reinsert_getD (j : ℕ) (T : List SourceSlot) (u h : List SmallSlot)
    (hu : u.length = (Template.extracted j T).length)
    (hh : h.length = (Template.remainder j T).length)
    (i : Fin T.length) (d : SmallSlot) :
    (Template.reinsert j T u h)[i.val]?.getD d =
      Sum.elim (fun k => u[k.val]?.getD d) (fun k => h[k.val]?.getD d)
        (splitPositions j T i) := by
  induction T generalizing u h with
  | nil => exact Fin.elim0 i
  | cons q T ih =>
    by_cases hq : q.role = .compensation j
    · cases u with
      | nil => simp [Template.extracted, hq] at hu
      | cons a u =>
        have hu' : u.length = (Template.extracted j T).length := by
          simpa [Template.extracted, hq] using hu
        have hh' : h.length = (Template.remainder j T).length := by
          simpa [Template.remainder, hq] using hh
        refine Fin.cases ?_ (fun i => ?_) i
        · simp [Template.reinsert, splitPositions, hq, finCongr, Fin.cast,
            Equiv.trans_apply, Equiv.sumCongr_apply]
        · have ht := ih u h hu' hh' i
          cases hi : splitPositions j T i with
          | inl k =>
            simpa [Template.reinsert, splitPositions, hq, hi, finCongr, Fin.cast,
              Equiv.trans_apply, Equiv.sumCongr_apply] using ht
          | inr k =>
            simpa [Template.reinsert, splitPositions, hq, hi,
              Equiv.trans_apply, Equiv.sumCongr_apply] using ht
    · cases h with
      | nil => simp [Template.remainder, hq] at hh
      | cons a h =>
        have hu' : u.length = (Template.extracted j T).length := by
          simpa [Template.extracted, hq] using hu
        have hh' : h.length = (Template.remainder j T).length := by
          simpa [Template.remainder, hq] using hh
        refine Fin.cases ?_ (fun i => ?_) i
        · simp [Template.reinsert, splitPositions, hq,
            Equiv.trans_apply, Equiv.sumCongr_apply]
        · have ht := ih u h hu' hh' i
          cases hi : splitPositions j T i with
          | inl k =>
            simpa [Template.reinsert, splitPositions, hq, hi, finCongr, Fin.cast,
              Equiv.trans_apply, Equiv.sumCongr_apply] using ht
          | inr k =>
            simpa [Template.reinsert, splitPositions, hq, hi,
              Equiv.trans_apply, Equiv.sumCongr_apply] using ht

theorem restoringAssignment_value (sources : SourceFamily) (j : ℕ)
    (T : List SourceSlot) (x : SourceAssignment sources T) (i : Fin T.length) :
    (x i).val = Sum.elim
      (fun u => ((restoringAssignmentEquiv sources j T x).1 u).val)
      (fun r => ((restoringAssignmentEquiv sources j T x).2 r).val)
      (splitPositions j T i) := by
  let d : SmallSlot := ⟨.bulk,0,0⟩
  have hr := reinsert_getD j T
    (assignedSlots sources (Template.extracted j T) (restoringAssignmentEquiv sources j T x).1)
    (assignedSlots sources (Template.remainder j T) (restoringAssignmentEquiv sources j T x).2)
    (assignedSlots_length _ _ _) (assignedSlots_length _ _ _) i d
  rw [←assignedSlots_split_reinsert] at hr
  cases hi : splitPositions j T i with
  | inl u =>
    rw [hi] at hr
    have hv := congrArg SmallSlot.value hr
    simpa [assignedSlots,Template.sample,i.isLt,u.isLt] using hv
  | inr r =>
    rw [hi] at hr
    have hv := congrArg SmallSlot.value hr
    simpa [assignedSlots,Template.sample,i.isLt,r.isLt] using hv

theorem restoringAssignment_value_inl (sources : SourceFamily) (j : ℕ)
    (T : List SourceSlot) (x : SourceAssignment sources T) (i : Fin T.length)
    (u : Fin (Template.extracted j T).length) (hi : splitPositions j T i=.inl u) :
    (x i).val=((restoringAssignmentEquiv sources j T x).1 u).val := by
  simpa only [hi,Sum.elim_inl] using restoringAssignment_value sources j T x i

theorem restoringAssignment_value_inr (sources : SourceFamily) (j : ℕ)
    (T : List SourceSlot) (x : SourceAssignment sources T) (i : Fin T.length)
    (r : Fin (Template.remainder j T).length) (hi : splitPositions j T i=.inr r) :
    (x i).val=((restoringAssignmentEquiv sources j T x).2 r).val := by
  simpa only [hi,Sum.elim_inr] using restoringAssignment_value sources j T x i

theorem splitPositions_slot_inl (j : ℕ) (T : List SourceSlot) (i : Fin T.length)
    (u : Fin (Template.extracted j T).length) (hi : splitPositions j T i=.inl u) :
    T.get i=(Template.extracted j T).get u := by
  simpa only [hi,Sum.elim_inl] using splitPositions_slot j T i

theorem splitPositions_slot_inr (j : ℕ) (T : List SourceSlot) (i : Fin T.length)
    (r : Fin (Template.remainder j T).length) (hi : splitPositions j T i=.inr r) :
    T.get i=(Template.remainder j T).get r := by
  simpa only [hi,Sum.elim_inr] using splitPositions_slot j T i

end Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatching

end

end OAI
