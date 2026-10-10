import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedCoordinatesSmall
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelReplacementGiantFree

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
local instance correctedKernelCoordinatesProductInternalDecidable (seed : List SourceSlot) (l : ℕ) :
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

theorem probabilityProduct_eq_restored_referenceSample (mixed : Bool)
    (u : SelectedBulkSample C l) :
    probabilityProduct (R.frame (l:=l) he hprime) mixed
      (fibreAssignment C (outerNonbulk C l p o) u)=
    ∏r : Representative (R.blockReference (l:=l) he).left.history (R.blockReference (l:=l) he).right.history,
      actualProbability mixed (R.blockReference (l:=l) he).left.history (R.blockReference (l:=l) he).right.history
        (R.blockReference (l:=l) he).left.supported (R.blockReference (l:=l) he).right.supported r
        ((referenceSample (C:=C) (l:=l) (R.blockReference (l:=l) he) (restoreOriginalDraw C l p o u)
          (representativeMap (R.blockReference (l:=l) he).left.history (R.blockReference (l:=l) he).right.history r)).toNat)
        (referenceSample (C:=C) (l:=l) (R.blockReference (l:=l) he) (restoreOriginalDraw C l p o u)) := by
  unfold probabilityProduct
  apply Finset.prod_congr rfl
  intro r _
  rw [R.restored_referenceSample_representative he u r,Int.toNat_natCast]
  exact actualProbability_congr_small mixed _ _ _ _ r _ _ _
    (R.fixedB_eq_restored_referenceSample_small he hprime u)

theorem restored_sampledJacobian_eq (u : SelectedBulkSample C l) :
    sampledJacobian (C:=C) (l:=l) (R.blockReference (l:=l) he)
      (referenceSample (C:=C) (l:=l) (R.blockReference (l:=l) he) (restoreOriginalDraw C l p o u))=
        ∏q : Block p,((outerBlocks C l p o q).val:ℝ) := by
  unfold sampledJacobian
  simp only [R.restored_referenceSample_representative,Int.toNat_natCast]
  exact representative_product_eq_blocks _ (R.blockReference (l:=l) he).left.history
    (R.blockReference (l:=l) he).right.history (R.blockReference (l:=l) he).left.labels (R.blockReference (l:=l) he).right.labels p
    (R.blockReference (l:=l) he).natDraw (R.blockReference (l:=l) he).slot_values (fun n:ℕ=>(n:ℝ))

end CorrectedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
