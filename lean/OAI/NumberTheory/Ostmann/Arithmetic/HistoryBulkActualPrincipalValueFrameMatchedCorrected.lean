import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualCorrectedPrincipalBlockFamilyData
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalValueFrameScalars
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatchingBulk

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalValueFrameMatched
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkIndependentFibreReference
open HistoryBulkActualPrincipalBlockFamily HistoryBulkActualGoodPrincipal
open HistoryPairPattern HistoryDiagonalRemainingRootMatching
open HistoryBulkFibreGiantApproximation HistoryBulkActualCorrectedPrincipalBlockFamily
open HistoryBulkFibreIntegralReplacementFrame HistoryBulkFibreSourceMean
open HistoryBulkPrincipalCollisionError HistoryBulkActualPrincipalValueFrame
attribute [local instance] Classical.propDecidable
local instance correctedValueFrameInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {outside : List ℕ}{e : RemainingPermutation (k:=k) (L:=L) (l:=l)}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}

theorem correctedPrincipalData_value_eq_frame
    (R : CorrectedSelectedOuter C p o outside e i)
    (he : PreservesRemainingBands _ e)
    (hlen : outside.length=2*(bulkSize k L/2)) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
    (corrected mixed : Bool) (u : SelectedBulkSample C l) :
    (principalData R he (bulkSize k L/2) hlen hp hV).value corrected mixed u =
      (R.frame he hp).rootValue mixed hV R.permutation
        (HistoryBulkFibreOriginalReference.fibreAssignment C (outerNonbulk C l p o) u) *
      giantValue (R.frame he hp) corrected mixed
        (HistoryBulkFibreOriginalReference.fibreAssignment C (outerNonbulk C l p o) u) := by
  rw [giantValue_eq_giantScalar]
  simp only [MatchedPrincipalReferenceData.value,MatchedPrincipalReferenceData.amplitude,
    PrincipalAmplitudeData.value,principalData,
    HistoryBulkActualCorrectedReferenceFamily.matchedWitnessPrincipalData,
    Frame.rootValue,sourceBulkUnits_fibreAssignment,inducedBulkPermutation_fullPermutation,
    CorrectedSelectedOuter.permutation]
  rfl

end Ostmann.Arithmetic.HistoryBulkActualPrincipalValueFrameMatched

end

end OAI
