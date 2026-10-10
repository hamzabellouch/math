import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatching
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatchingPositionsValues

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatching
open Construction HistoryDiagonalCorrectedOriginalMean

theorem restoredCounterpart_value (sources : SourceFamily) (j : ℕ) (T : List SourceSlot)
    (x : SourceAssignment sources T)
    (e : Equiv.Perm (RemainingIndex (Template.remainder j T)))
    (he : PreservesRemainingBands (Template.remainder j T) e)
    (hc : SmallCounterpartCompatible sources _ (restoringAssignmentEquiv sources j T x).2 e)
    (i : Fin T.length) :
    (restoredCounterpart sources j T x e hc i).val = (x (fullPermutation j T e he i)).val := by
  rw [restoringAssignment_value sources j T (restoredCounterpart sources j T x e hc) i,
    restoringAssignment_value sources j T x (fullPermutation j T e he i)]
  simp only [restoredCounterpart, Equiv.apply_symm_apply, split_fullPermutation]
  cases splitPositions j T i with
  | inl u => rfl
  | inr v => exact reconstructSmallCounterpart_val sources _ _ e he hc v

end Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatching

end

end OAI
