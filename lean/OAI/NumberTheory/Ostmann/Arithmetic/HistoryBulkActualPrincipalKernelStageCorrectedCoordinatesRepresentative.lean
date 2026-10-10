import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedCoordinates
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelProductReplacementMatchedRepresentative

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
local instance correctedKernelCoordinatesRepresentativeInternalDecidable (seed : List SourceSlot) (l : ℕ) :
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

theorem restored_referenceSample_representative (u : SelectedBulkSample C l)
    (r : Representative (R.blockReference (l:=l) he).left.history (R.blockReference (l:=l) he).right.history) :
    referenceSample (C:=C) (l:=l) (R.blockReference (l:=l) he) (restoreOriginalDraw C l p o u)
      (representativeMap (R.blockReference (l:=l) he).left.history (R.blockReference (l:=l) he).right.history r)=
      (prime (R.blockReference (l:=l) he).left.history (R.blockReference (l:=l) he).right.history r:ℤ) := by
  exact (matchedReferenceSample_representative (R.blockReference (l:=l) he)
    (fun _=>C.giant) (restoreOriginalDraw C l p o u) r).trans
      (congrArg (fun n:ℕ=>(n:ℤ)) (matchedReference_prime (R.blockReference (l:=l) he) r).symm)

end CorrectedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
