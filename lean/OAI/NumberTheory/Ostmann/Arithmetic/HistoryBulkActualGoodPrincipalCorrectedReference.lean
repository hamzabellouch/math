import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalCorrectedReferenceFrame
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatchingActual

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
open HistoryCompensationRepresentativePatterns HistoryDiagonalRemainingRootMatching
open HistoryPairBulkCoordinates CanonicalHistoryLeafBulk HistoryBulkFibreOriginalReference
attribute [local instance] Classical.propDecidable
local instance actualGoodCorrectedReferenceInternalDecidable (seed : List SourceSlot) (l : ℕ) :
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

theorem representative_prime (q : Block p) :
    prime (R.frame he hprime).left (R.frame he hprime).right
      (R.representative he hprime q)=(outerBlocks C l p o q).val := by
  change prime (R.blockReference he).left.history (R.blockReference he).right.history
    ((typedBlockEquiv (R.blockReference he).left (R.blockReference he).right p
      (R.blockReference he).natDraw (R.blockReference he).slot_values).symm q)=_
  exact (representativeBlockEquiv_prime _ (R.blockReference he).left.history
    (R.blockReference he).right.history (R.blockReference he).left.labels
    (R.blockReference he).right.labels p (R.blockReference he).natDraw
    (R.blockReference he).slot_values _).trans
      (congrArg (R.blockReference he).natDraw.val
        ((typedBlockEquiv (R.blockReference he).left (R.blockReference he).right p
          (R.blockReference he).natDraw (R.blockReference he).slot_values).apply_symm_apply q))

theorem permutation_eq_bulkPermutation :
    R.permutation=HistoryBulkIndependentFibreReference.bulkPermutation e he := by
  symm
  exact inducedBulkPermutation_fullPermutation (2*(bulkSize k L/2)) k l e he

theorem frame_bulkSamples (u : Fin (2^l)×Fin (2*(bulkSize k L/2))) :
    bulkSamples C.sources (2*(bulkSize k L/2)) k l (R.frame he hprime).rightSource u.1 u.2=
      bulkSamples C.sources (2*(bulkSize k L/2)) k l (R.frame he hprime).leftSource
        (R.permutation u).1 (R.permutation u).2 :=
  counterpartCurrentAssignment_remainingBulkSamples C
    (fibreAssignment C (outerNonbulk C l p o) R.witness.bulk) e he R.witness.compatible u

end CorrectedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
