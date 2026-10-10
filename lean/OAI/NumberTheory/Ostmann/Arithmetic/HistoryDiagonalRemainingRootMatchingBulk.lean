import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatching
import OAI.NumberTheory.Ostmann.Construction.DiagonalPermutationCount

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatching
open Construction Conclusion

theorem splitPositions_inr_val (j : ℕ) (T : List SourceSlot) (i : Fin T.length)
    (r : Fin (Template.remainder j T).length) (h : splitPositions j T i = Sum.inr r) :
    r.val = (Template.remainder j (T.take i.val)).length := by
  induction T with
  | nil => exact Fin.elim0 i
  | cons q T ih =>
    revert h
    by_cases hq : q.role = .compensation j
    · refine Fin.cases ?_ (fun i => ?_) i <;> intro h
      · simp [splitPositions, hq, Equiv.trans_apply, Equiv.sumCongr_apply] at h
      · cases hi : splitPositions j T i with
        | inl u =>
          simp [splitPositions, hq, hi, Equiv.trans_apply, Equiv.sumCongr_apply] at h
        | inr u =>
          have ht := ih i u hi
          unfold Template.remainder at ht
          simp only [decide_not] at ht
          simp [splitPositions, hq, hi, Equiv.trans_apply, Equiv.sumCongr_apply,
            Fin.ext_iff] at h
          simp [Template.remainder, hq, ← ht, h]
    · refine Fin.cases ?_ (fun i => ?_) i <;> intro h
      · simp [splitPositions, hq, Equiv.trans_apply, Equiv.sumCongr_apply,
          Fin.ext_iff] at h
        simpa [Template.remainder] using h.symm
      · cases hi : splitPositions j T i with
        | inl u =>
          simp [splitPositions, hq, hi, Equiv.trans_apply, Equiv.sumCongr_apply] at h
        | inr u =>
          have ht := ih i u hi
          unfold Template.remainder at ht
          simp only [decide_not] at ht
          simp [splitPositions, hq, hi, Equiv.trans_apply, Equiv.sumCongr_apply,
            Fin.ext_iff] at h
          simp [Template.remainder, hq, ← ht, ← h]

theorem take_replicate_flatten {α : Type*} (A : List α) (r b i : ℕ)
    (hb : b < r) (hi : i ≤ A.length) :
    ((List.replicate r A).flatten).take (b * A.length + i) =
      (List.replicate b A).flatten ++ A.take i := by
  induction b generalizing r with
  | zero =>
    cases r with
    | zero => omega
    | succ r => simp [List.replicate_succ, List.take_append, Nat.sub_eq_zero_of_le hi]
  | succ b ih =>
    cases r with
    | zero => omega
    | succ r =>
      have hb' : b < r := by omega
      have hlen : A.length ≤ (b+1)*A.length+i := by simp only [Nat.add_mul, Nat.one_mul]; omega
      have hoff : (b+1)*A.length+i-A.length=b*A.length+i := by simp only [Nat.add_mul, Nat.one_mul]; omega
      simp only [List.replicate_succ, List.flatten_cons, List.take_append]
      rw [List.take_of_length_le hlen, hoff, ih r hb', List.append_assoc]

 theorem remainder_take_current_bulk_length (m k l : ℕ) (b : Fin (2^l)) (i : Fin m) :
    (Template.remainder (l+1) ((Template.current (Template.initial m k) l).take
      (b.val*(bulkLeafTemplate m k l).length+i.val))).length =
        b.val*(bulkLeafTemplate m k (l+1)).length+i.val := by
  rw [current_eq_bulkLeafBlocks, take_replicate_flatten _ _ _ _ b.isLt
    (i.isLt.le.trans (bulkLeafTemplate_length_ge m k l))]
  have hp : (bulkLeafTemplate m k l).take i.val=(initialBulkSlots m).take i.val := by
    simp only [bulkLeafTemplate, List.take_append]
    simp [Nat.sub_eq_zero_of_le (i.isLt.le)]
  have hf : Template.remainder (l+1) ((initialBulkSlots m).take i.val)=
      (initialBulkSlots m).take i.val := by
    apply List.filter_eq_self.mpr
    intro q hq
    have hmem := List.mem_of_mem_take hq
    obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hmem
    simp
  simp only [Template.remainder, List.filter_append, List.filter_flatten,
    List.map_replicate, List.length_append, List.length_flatten, List.map_replicate,
    List.sum_replicate]
  change b.val*(Template.remainder (l+1) (bulkLeafTemplate m k l)).length +
      (Template.remainder (l+1) ((bulkLeafTemplate m k l).take i.val)).length = _
  rw [← bulkLeafTemplate_succ, hp, hf]
  simp

@[simp] theorem remainderSlotBulkEquiv_symm_val (m k l : ℕ)
    (b : Fin (2^l)) (i : Fin m) :
    ((DiagonalPermutationCount.remainderSlotBulkEquiv m k l).symm (b,i)).val.val =
      b.val*(bulkLeafTemplate m k (l+1)).length+i.val := by
  change ((DiagonalPermutationCount.remainderPositionBlockEquiv m k l).symm (b,
    ⟨i.val, i.isLt.trans_le (bulkLeafTemplate_length_ge m k (l+1))⟩)).val = _
  exact DiagonalPermutationCount.remainderPositionBlockEquiv_symm_val m k l b _

theorem splitPositions_current_bulk (m k l : ℕ) (u : Fin (2^l) × Fin m) :
    splitPositions (l+1) (Template.current (Template.initial m k) l)
      ((currentBulkPositionEquiv m k l).symm u).val =
        Sum.inr ((DiagonalPermutationCount.remainderSlotBulkEquiv m k l).symm u).val := by
  rcases u with ⟨b,i⟩
  cases hs : splitPositions (l+1) (Template.current (Template.initial m k) l)
      ((currentBulkPositionEquiv m k l).symm (b,i)).val with
  | inl q =>
    have hb := ((currentBulkPositionEquiv m k l).symm (b,i)).property
    change ((Template.current (Template.initial m k) l).get
      ((currentBulkPositionEquiv m k l).symm (b,i)).val).role = .bulk at hb
    rw [splitPositions_slot, hs] at hb
    simp only [Sum.elim_inl] at hb
    have hmem := List.mem_filter.mp (List.get_mem
      (Template.extracted (l+1) (Template.current (Template.initial m k) l)) q)
    have hrole := of_decide_eq_true hmem.2
    rw [hrole] at hb
    contradiction
  | inr r =>
    have hv := splitPositions_inr_val (l+1) _ _ r hs
    rw [currentBulkPositionEquiv_symm_val, remainder_take_current_bulk_length] at hv
    congr 1
    apply Fin.ext
    rw [remainderSlotBulkEquiv_symm_val]
    exact hv

theorem smallPermutation_remainder_bulk (m k l : ℕ)
    (e : Equiv.Perm (RemainingIndex (DiagonalPermutationCount.remainingTemplate m k l)))
    (he : PreservesRemainingBands (DiagonalPermutationCount.remainingTemplate m k l) e)
    (u : Fin (2^l) × Fin m) :
    smallPermutation e he ((DiagonalPermutationCount.remainderSlotBulkEquiv m k l).symm u).val =
      ((DiagonalPermutationCount.remainderSlotBulkEquiv m k l).symm
        (DiagonalPermutationCount.remainingBulkPermutation m k l e u)).val := by
  apply Fin.succ_injective
  rw [smallPermutation_succ]
  exact (DiagonalPermutationCount.remainingBulkPermutation_apply m k l e he u).symm

theorem inducedBulkPermutation_fullPermutation (m k l : ℕ)
    (e : Equiv.Perm (RemainingIndex (DiagonalPermutationCount.remainingTemplate m k l)))
    (he : PreservesRemainingBands (DiagonalPermutationCount.remainingTemplate m k l) e) :
    HistoryBulkIndependentReferenceFrequency.inducedBulkPermutation m k l
      (fullPermutation (l+1) (Template.current (Template.initial m k) l) e he)
      (fullPermutation_bulk (l+1) (Template.current (Template.initial m k) l) e he) =
        DiagonalPermutationCount.remainingBulkPermutation m k l e := by
  apply Equiv.ext
  intro u
  apply (DiagonalPermutationCount.remainderSlotBulkEquiv m k l).symm.injective
  apply Subtype.ext
  apply Sum.inr_injective (α := Fin (Template.extracted (l+1)
    (Template.current (Template.initial m k) l)).length)
  rw [← splitPositions_current_bulk,
    HistoryBulkIndependentReferenceFrequency.inducedBulkPermutation_position,
    split_fullPermutation, splitPositions_current_bulk]
  simp only [Sum.map_inr]
  rw [smallPermutation_remainder_bulk]

end Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatching

end

end OAI
