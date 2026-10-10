import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionCorrectedBasic

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
local instance correctedCollisionValueInternalDecidable (seed : List SourceSlot) (l : ℕ) :
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

@[simp] theorem collisionReference_amplitudeAt (u : SelectedBulkSample C l) :
    (R.collisionReference he hlen hp hV).amplitudeAt u=
      (principalData R he (bulkSize k L/2) hlen hp hV).amplitude u :=
  HistoryBulkActualPrincipalCollisionCorrected.fromMatchedData_amplitudeAt _ _ _ _ u

theorem collisionReference_value (corrected mixed : Bool) (u : SelectedBulkSample C l) :
    (R.collisionReference he hlen hp hV).value corrected mixed u=
      (principalData R he (bulkSize k L/2) hlen hp hV).value corrected mixed u :=
  HistoryBulkActualPrincipalCollisionCorrected.fromMatchedData_value _ _ _ _ corrected mixed u

theorem collisionReference_value_eq_frame (corrected mixed : Bool) (u : SelectedBulkSample C l) :
    (R.collisionReference he hlen hp hV).value corrected mixed u=
      (R.frame he hp).rootValue mixed hV R.permutation
        (fibreAssignment C (outerNonbulk C l p o) u) *
      giantValue (R.frame he hp) corrected mixed
        (fibreAssignment C (outerNonbulk C l p o) u) :=
  (R.collisionReference_value he hlen hp hV corrected mixed u).trans
    (correctedPrincipalData_value_eq_frame R he hlen hp hV corrected mixed u)

theorem collisionReference_density_value (u : SelectedBulkSample C l) :
    Frame.extractedDensity (C:=C) (R.frame he hp).leftSource *
        (R.collisionReference he hlen hp hV).value true true u=
      Frame.extractedDensity (C:=C) (R.frame he hp).leftSource *
        ((R.frame he hp).rootValue true hV R.permutation
          (fibreAssignment C (outerNonbulk C l p o) u) *
          giantValue (R.frame he hp) true true
            (fibreAssignment C (outerNonbulk C l p o) u)) :=
  congrArg (fun z : ℂ => Frame.extractedDensity (C:=C) (R.frame he hp).leftSource * z)
    (R.collisionReference_value_eq_frame he hlen hp hV true true u)

end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal.CorrectedSelectedOuter

end

end OAI
