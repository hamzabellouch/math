import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualCorrectedReferenceFamilyMatchedMetadata
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalCorrectedReferenceFrame
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuter
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelProductReplacementMatchedSelectedSupport

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualPrincipalBlockFamily
open HistoryBulkActualRootReferenceFamily HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference
open HistoryBulkIndependentFibreReference HistoryPairPattern HistoryPairReferenceSourceTransport
open HistoryPairKernelProductReplacement HistoryDiagonalRemainingRootMatching
attribute [local instance] Classical.propDecidable
local instance correctedSourceSupportCoordinatesInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _ => C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {outside : List ℕ} {e : RemainingPermutation (k:=k) (L:=L) (l:=l)}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}
namespace CorrectedSelectedOuter
variable (R : CorrectedSelectedOuter C p o outside e i)

theorem matchedReferenceSample_right_assignment (he : PreservesRemainingBands _ e)
    (y : OriginalDraw (fun _ => C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (ho : originalDrawOuter (fun _ => C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p y = o)
    (hc : Compatible C (outerNonbulk C l p o) e (originalDrawBulk C l p y))
    (j : Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length) :
    matchedReferenceSample (R.blockReference he) (fun _ => C.giant) y
      (rightMap (R.blockReference he).left.history (R.blockReference he).right.history
        (.inr (.inl (rootPosition (R.blockReference he).right j)))) =
      ((rightAssignment C (outerNonbulk C l p o) e (originalDrawBulk C l p y) hc j).val : ℤ) := by
  have halign := HistoryBulkActualCorrectedReferenceFamily.matchedWitnessBlockReference_rootAligned
    C p R.data.blockDraw R.data.valid outside (outerNonbulk C l p o) e
    i.1.val i.1.val i.2.1 i.2.2 R.witness he
  have hindex := matchedRightRootIndex_eq_of_aligned (R.blockReference he)
    (fullPermutation (l+1) _ e he) halign
  rw [matchedReferenceSample_right_root,hindex]
  have hx := originalDrawAssignment_eq_fibreAssignment C l p y
  rw [ho] at hx
  change ((originalDrawAssignment C l p y (fullPermutation (l+1) _ e he j)).val : ℤ) = _
  rw [hx]
  exact (congrArg (fun n : ℕ => (n : ℤ))
    (counterpartCurrentAssignment_value C
      (fibreAssignment C (outerNonbulk C l p o) (originalDrawBulk C l p y)) e he hc j)).symm

end CorrectedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
