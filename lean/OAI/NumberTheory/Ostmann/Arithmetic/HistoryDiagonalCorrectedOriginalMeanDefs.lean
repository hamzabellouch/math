import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMeanDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMeanRestore

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMean
open Construction Conclusion HistorySignedResidues HistorySignedXiTransport HistorySymbolicEncoding
open HistoryGiantReferenceMean HistoryGiantPriorGrid HistoryCRTIntegration
open HistoryDiagonalSmallAverage HistorySignedResidueFactorization
open HistoryGiantOriginalMeanFactorization hiding originalMixedMean
open HistoryDiagonalSmallOriginalMean hiding originalMixedMean
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

def originalMixedMean (outside : List ℕ)
    (x y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (s t : ℤ) (c e : Choices (l:=l) C) : ℂ :=
  mixedMean C.giantCenter C.giant
    (sourceIntegrand d C.sources _ (frequencyBound Bs BD Bz k L) outside l
      (sourceState C.sources _ x s) (sourceState C.sources _ y t) c e
      (fun P Q => (smallMultiplier C outside x s P Q:ℂ) * counterpart C y Q)
      (bulkSize k L/2) (bulkSize k L/2) C.scale C.bulkBin C.spectatorBin C.giantCenter)

theorem counterpart_nat_eq_remainingCounterpart
    (y : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (q : C.giant.Sample) :
    counterpart C y (q.val:ℤ) =
      (remainingCounterpart C.sources (Current (k:=k) (L:=L) (l:=l)) (l+1) C.giant
        ((C.giantCenter:ℝ)+C.compensationLogScale l+stepGap BD Bz k L l)
        (C.compensationLogScale l) C.giantCenter (C.cells.center (bulkSize k L/2))
        (outerAssignment C y) (q,smallAssignment C y):ℂ) := by
  simp only [counterpart,Int.cast_natCast]
  rw [HistoryGiantReferenceCounterpart.remainingCounterpartAt_sample C.sources _ (l+1) C.giant
    _ _ _ _ (outerAssignment C y) (q,smallAssignment C y)]

end Ostmann.Arithmetic.HistoryDiagonalCorrectedOriginalMean

end

end OAI
