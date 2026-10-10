import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalCorrectedReferenceFrame
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterEquivBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCoordinatesRoot
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReferenceBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatchedBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualPrincipalBlockFamily
open HistoryBulkActualRootReferenceFamily HistoryBulkSourceDisintegration
open HistoryBulkIndependentFibreReference HistoryBulkFibreGiantApproximation
open HistoryPairRepresentatives HistoryPairReferenceSourceTransport
attribute [local instance] Classical.propDecidable
local instance correctedKernelCoordinatesInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {outside : List ℕ} {e : RemainingPermutation (k:=k) (L:=L) (l:=l)}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}
namespace CorrectedSelectedOuter
variable (R : CorrectedSelectedOuter C p o outside e i)
  (he : PreservesRemainingBands _ e) (hprime : ∀q∈outside,q.Prime)

open HistoryBulkFibreOriginalReference
open HistoryPairPattern HistoryPairBulkCoordinates HistoryPairRepresentativeVariables HistoryPairBulkTransport
open HistoryPairKernelReplacement HistoryPairKernelProductReplacement
open HistoryBulkPrincipalKernelReplacementMatched HistoryBulkPrincipalBSquareReference
open HistoryBulkReferenceTests HistoryBulkReferenceScalarCoordinates
open HistoryCompensationRepresentativePatterns HistoryOccurrenceVariables

theorem fixedB_root (u : SelectedBulkSample C l)
    (j : Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length) :
    (R.frame (l:=l) he hprime).fixedB (fibreAssignment C (outerNonbulk C l p o) u)
      (rootKey (R.frame (l:=l) he hprime).left (R.frame (l:=l) he hprime).right
        (rootPosition (leftDraw (R.frame (l:=l) he hprime)) j)) =
      ((fibreAssignment C (outerNonbulk C l p o) u j).val : ℤ) := by
  exact HistoryBulkPrincipalBSquareReference.fixedB_root (R.frame (l:=l) he hprime)
    (fibreAssignment C (outerNonbulk C l p o) u)
    (fibreAssignment_nonbulk_fixed C (outerNonbulk C l p o) u R.witness.bulk) j

end CorrectedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
