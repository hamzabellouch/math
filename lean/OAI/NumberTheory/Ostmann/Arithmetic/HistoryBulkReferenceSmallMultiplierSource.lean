import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceSmallUnitDataReferenceActual
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallOriginalMeanDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueWeightedAverages

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceSmallMultiplier
open Construction Conclusion HistoryPairBulkTransport
open HistoryGiantOriginalMeanFactorization HistoryDiagonalSmallOriginalMean
open HistoryDiagonalSmallAverage HistoryBulkReferenceSmallUnitData
open DiagonalSmallResidueNorm HistoryCRTIntegration
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

abbrev currentSmallHistory
    (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (s : ℤ) (c : Choices (l:=l) C) : History l :=
  assignedHistory C.sources (Seed (k:=k) (L:=L)) (frequencyBound Bs BD Bz k L) l s 1 1 x c

abbrev currentOuterSlots
    (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l))) : List SmallSlot :=
  assignedSlots C.sources _ (outerAssignment C x)

abbrev currentRemainingSlots
    (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l))) : List SmallSlot :=
  assignedSlots C.sources _ (smallAssignment C x)

theorem currentSmallHistory_split
    (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (s : ℤ) (c : Choices (l:=l) C) :
    (currentSmallHistory C x s c).root.small.Perm
      (currentOuterSlots C x ++ currentRemainingSlots C x) := by
  simp only [currentSmallHistory, assignedHistory, decodeHistory_root, assignedRoot]
  change (assignedSlots C.sources _ x).Perm _
  rw [assignedSlots_split_reinsert C.sources (l+1) _ x]
  exact Template.reinsert_perm _ _ _ _ (assignedSlots_length _ _ _) (assignedSlots_length _ _ _)

theorem currentSmallPrimeFacts
    (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (s : ℤ) (c : Choices (l:=l) C) :
    ∀ i, Fact (smallPrime (currentRemainingSlots C x) (currentOuterSlots C x) i).Prime :=
  stateSmallPrimeFacts (currentSmallHistory C x s c).root
    (assigned_root_primeSmall C.sources _ _ l s 1 1 x c)
    (currentOuterSlots C x) (currentRemainingSlots C x) (currentSmallHistory_split C x s c)

def currentRootSmallTest (outside : List ℕ)
    (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (s : ℤ) (c : Choices (l:=l) C)
    (hu : SmallUnitData outside.prod 1 1 (currentOuterSlots C x) (currentRemainingSlots C x) s) :
    MixedPair (rootModulus (currentSmallHistory C x s c)) → ℂ :=
  letI := currentSmallPrimeFacts C x s c
  fun z => (rootSmallTest d (currentSmallHistory C x s c)
    (currentOuterSlots C x) (currentRemainingSlots C x) (currentSmallHistory_split C x s c)
    outside.prod 1 1 s hu z : ℂ)

end Ostmann.Arithmetic.HistoryBulkReferenceSmallMultiplier

end

end OAI
