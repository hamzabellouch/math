import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualCorrectedReferenceFamilyMatchedMetadata
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalCorrectedReferenceFrame

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualCorrectedPrincipalBlockFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkIndependentFibreReference
open HistoryBulkActualPrincipalBlockFamily HistoryBulkActualGoodPrincipal
open HistoryPairPattern HistoryDiagonalRemainingRootMatching
attribute [local instance] Classical.propDecidable
local instance actualCorrectedPrincipalDataInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {outside : List ℕ}{e : RemainingPermutation (k:=k) (L:=L) (l:=l)}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}
  (R : CorrectedSelectedOuter C p o outside e i)(he : PreservesRemainingBands _ e)

theorem reference_giants : RootGiantsAgree (R.blockReference he).left.history
    (R.blockReference he).right.history :=
  HistoryBulkActualCorrectedReferenceFamily.matchedWitnessBlockReference_giants C p
    R.data.blockDraw R.data.valid outside (outerNonbulk C l p o) e
    i.1.val i.1.val i.2.1 i.2.2 R.witness he

theorem reference_rootAligned
    (j : Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length) :
    coordinateSample _ (R.blockReference he).right.history (R.blockReference he).right.labels (.inr (.inl j))=
      coordinateSample _ (R.blockReference he).left.history (R.blockReference he).left.labels
        (.inr (.inl (fullPermutation (l+1) _ e he j))) :=
  HistoryBulkActualCorrectedReferenceFamily.matchedWitnessBlockReference_rootAligned C p
    R.data.blockDraw R.data.valid outside (outerNonbulk C l p o) e
    i.1.val i.1.val i.2.1 i.2.2 R.witness he j

def principalData (n : ℕ)(hlen : outside.length=2*n)(hprime : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) :
    MatchedPrincipalReferenceData C (R.blockReference he) :=
  HistoryBulkActualCorrectedReferenceFamily.matchedWitnessPrincipalData C p
    R.data.blockDraw R.data.valid outside (outerNonbulk C l p o) e
    i.1.val i.1.val i.2.1 i.2.2 R.witness he R.data.nonbulk_pos
    (R.data.left_mass i) (R.data.right_mass i) n hlen hprime hV true

end Ostmann.Arithmetic.HistoryBulkActualCorrectedPrincipalBlockFamily

end

end OAI
