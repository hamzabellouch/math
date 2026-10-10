import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceSmallMultiplierBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferenceSmallMultiplierSource

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceSmallMultiplier
open Construction Conclusion HistoryPairBulkTransport
open HistoryGiantOriginalMeanFactorization HistoryDiagonalSmallOriginalMean
open HistoryDiagonalSmallAverage HistoryBulkReferenceSmallUnitData
open DiagonalSmallResidueNorm HistoryCRTIntegration
open HistorySignedResidueFactorization HistorySignedResidueWeightedAverages
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E)

theorem smallMultiplier_mul_currentRootIndicator (outside : List ℕ)
    (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (s : ℤ) (c : Choices (l:=l) C)
    (hu : SmallUnitData outside.prod 1 1 (currentOuterSlots C x) (currentRemainingSlots C x) s)
    (P Q : ℤ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    (smallMultiplier C outside x s P Q : ℂ) *
      rootResidueIndicator (currentSmallHistory C x s c) (P,Q) =
    rootResidueIndicator (currentSmallHistory C x s c) (P,Q) *
      mixedExtension (currentRootSmallTest C outside x s c hu) (P,Q) := by
  have := currentSmallPrimeFacts C x s c
  exact diagonalSmallMultiplier_mul_rootResidueIndicator_intCast d
    (currentSmallHistory C x s c) (currentOuterSlots C x) (currentRemainingSlots C x)
    (currentSmallHistory_split C x s c) outside.prod 1 1 P Q s hu hP hQ

theorem smallMultiplier_mul_currentRootFactor (outside : List ℕ)
    (x : SourceAssignment C.sources (Current (k:=k) (L:=L) (l:=l)))
    (s : ℤ) (c : Choices (l:=l) C)
    (hu : SmallUnitData outside.prod 1 1 (currentOuterSlots C x) (currentRemainingSlots C x) s)
    (P Q : ℤ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (R : ℂ) :
    (smallMultiplier C outside x s P Q : ℂ) *
      (rootResidueIndicator (currentSmallHistory C x s c) (P,Q) * R) =
    (rootResidueIndicator (currentSmallHistory C x s c) (P,Q) *
      mixedExtension (currentRootSmallTest C outside x s c hu) (P,Q)) * R := by
  rw [← mul_assoc, smallMultiplier_mul_currentRootIndicator C outside x s c hu P Q hP hQ]

end Ostmann.Arithmetic.HistoryBulkReferenceSmallMultiplier

end

end OAI
