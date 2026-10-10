import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedValue

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal.CorrectedSelectedOuter
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkIndependentFibreReference
open HistoryBulkActualPrincipalBlockFamily HistoryBulkActualGoodPrincipal
open HistoryPairPattern HistoryDiagonalRemainingRootMatching
open HistoryBulkFibreGiantApproximation HistoryBulkActualCorrectedPrincipalBlockFamily
open HistoryBulkFibreIntegralReplacementFrame HistoryBulkFibreSourceMean
open HistoryBulkPrincipalCollisionError HistoryBulkActualPrincipalValueFrame
open HistoryBulkActualPrincipalValueFrameMatched HistoryBulkFibreOriginalReference
open HistoryBulkReferencePeriodicMeanSource HistorySignedResidueFactorization
attribute [local instance] Classical.propDecidable
local instance correctedCollisionIntegralInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {outside : List ℕ}{e : RemainingPermutation (k:=k) (L:=L) (l:=l)}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}
  (R : CorrectedSelectedOuter C p o outside e i)
  (he : PreservesRemainingBands _ e)
  (hlen : outside.length=2*(bulkSize k L/2)) (hp : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

theorem collisionReference_cmean_eq_frame (corrected mixed : Bool) :
    (selectedBulkPrior C l).cmean (fun u=>
      (R.collisionReference he hlen hp hV).value corrected mixed u) =
    bulkMean (R.frame he hp) corrected mixed (outerNonbulk C l p o) R.permutation hV :=
  congrArg (selectedBulkPrior C l).cmean (funext
    (R.collisionReference_value_eq_frame he hlen hp hV corrected mixed))

end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal.CorrectedSelectedOuter

end

end OAI
