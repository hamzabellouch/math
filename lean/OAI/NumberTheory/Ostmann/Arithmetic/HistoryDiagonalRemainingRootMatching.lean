import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentReferenceFrequencyPermutation
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatchingBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatchingPositions
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkTransportAssigned

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatching
open Construction HistoryDiagonalCorrectedOriginalMean HistoryPairBulkTransport
open HistoryPairBulkCoordinates HistoryBulkIndependentReferenceFrequency

def fullPermutation (j : ℕ) (T : List SourceSlot)
    (e : Equiv.Perm (RemainingIndex (Template.remainder j T)))
    (he : PreservesRemainingBands (Template.remainder j T) e) : Equiv.Perm (Fin T.length) :=
  (splitPositions j T).trans
    ((Equiv.sumCongr (Equiv.refl _) (smallPermutation e he)).trans (splitPositions j T).symm)

@[simp] theorem split_fullPermutation (j : ℕ) (T : List SourceSlot)
    (e : Equiv.Perm (RemainingIndex (Template.remainder j T)))
    (he : PreservesRemainingBands (Template.remainder j T) e) (i : Fin T.length) :
    splitPositions j T (fullPermutation j T e he i) =
      Sum.map id (smallPermutation e he) (splitPositions j T i) := by
  simp [fullPermutation]

theorem fullPermutation_fixes_extracted (j : ℕ) (T : List SourceSlot)
    (e : Equiv.Perm (RemainingIndex (Template.remainder j T)))
    (he : PreservesRemainingBands (Template.remainder j T) e)
    (i : Fin T.length) (u : Fin (Template.extracted j T).length)
    (hi : splitPositions j T i = Sum.inl u) : fullPermutation j T e he i = i := by
  apply (splitPositions j T).injective
  rw [split_fullPermutation, hi]
  rfl

theorem fullPermutation_fixes_compensation (j : ℕ) (T : List SourceSlot)
    (e : Equiv.Perm (RemainingIndex (Template.remainder j T)))
    (he : PreservesRemainingBands (Template.remainder j T) e)
    (i : Fin T.length) (hi : (T.get i).role = .compensation j) :
    fullPermutation j T e he i = i := by
  cases hs : splitPositions j T i with
  | inl u => exact fullPermutation_fixes_extracted j T e he i u hs
  | inr r =>
    have hv := splitPositions_slot j T i
    simp only [hs, Sum.elim_inr] at hv
    have hm := List.get_mem (Template.remainder j T) r
    have hn : ((Template.remainder j T).get r).role ≠ .compensation j := by
      exact of_decide_eq_true (List.mem_filter.mp hm).2
    exact (hn (hv ▸ hi)).elim

theorem fullPermutation_role (j : ℕ) (T : List SourceSlot)
    (e : Equiv.Perm (RemainingIndex (Template.remainder j T)))
    (he : PreservesRemainingBands (Template.remainder j T) e) (i : Fin T.length) :
    (T.get (fullPermutation j T e he i)).role = (T.get i).role := by
  rw [splitPositions_slot j T (fullPermutation j T e he i), splitPositions_slot j T i,
    split_fullPermutation]
  cases splitPositions j T i with
  | inl u => rfl
  | inr v => exact smallPermutation_role e he v

theorem fullPermutation_bulk (j : ℕ) (T : List SourceSlot)
    (e : Equiv.Perm (RemainingIndex (Template.remainder j T)))
    (he : PreservesRemainingBands (Template.remainder j T) e) (i : Fin T.length) :
    (T.get i).role = .bulk ↔ (T.get (fullPermutation j T e he i)).role = .bulk := by
  rw [fullPermutation_role]

def restoredCounterpart (sources : SourceFamily) (j : ℕ) (T : List SourceSlot)
    (x : SourceAssignment sources T)
    (e : Equiv.Perm (RemainingIndex (Template.remainder j T)))
    (hc : SmallCounterpartCompatible sources _ (restoringAssignmentEquiv sources j T x).2 e) :
    SourceAssignment sources T :=
  (restoringAssignmentEquiv sources j T).symm
    ((restoringAssignmentEquiv sources j T x).1,
      reconstructSmallCounterpart sources _ (restoringAssignmentEquiv sources j T x).2 e hc)

end Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatching

end

end OAI
