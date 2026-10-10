import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterEquivBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedValue
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalKernelReplacementMatchedBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation
open HistoryBulkFibreOriginalReference HistoryBulkIndependentFibreReference
open HistoryPairRepresentatives HistoryPairKernelReplacement HistoryBulkReferencePeriodicMeanSource
open HistoryBulkActualPrincipalBlockFamily HistoryBulkActualCorrectedPrincipalBlockFamily
attribute [local instance] Classical.propDecidable
local instance correctedKernelStageRestoredInternalDecidable (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {outside : List ℕ} {e : RemainingPermutation (k:=k) (L:=L) (l:=l)}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}
namespace CorrectedSelectedOuter
variable (R : CorrectedSelectedOuter C p o outside e i)
  (he : PreservesRemainingBands _ e)
  (hout : outside.length=2*(bulkSize k L/2)) (hprime : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

def restoredKernelProduct (symbolic : Bool) (u : SelectedBulkSample C l) : ℝ :=
  let z := HistoryBulkPrincipalKernelReplacementMatched.referenceSample (R.blockReference he)
    (restoreOriginalDraw C l p o u)
  ∏q : Representative (R.blockReference he).left.history (R.blockReference he).right.history,
    if symbolic then symbolicKernel true (R.blockReference he).left.history (R.blockReference he).right.history
      (R.blockReference he).left.supported (R.blockReference he).right.supported q
      (z (HistoryPairRepresentativeVariables.representativeMap (R.blockReference he).left.history (R.blockReference he).right.history q)).toNat
    else actualProbability true (R.blockReference he).left.history (R.blockReference he).right.history
      (R.blockReference he).left.supported (R.blockReference he).right.supported q
      (z (HistoryPairRepresentativeVariables.representativeMap (R.blockReference he).left.history (R.blockReference he).right.history q)).toNat z

def restoredKernelTerm (symbolic : Bool) (u : SelectedBulkSample C l) : ℂ :=
  let r := R.frame he hprime
  let y := restoreOriginalDraw C l p o u
  let z := HistoryBulkPrincipalKernelReplacementMatched.referenceSample (R.blockReference he) y
  Frame.extractedDensity (C:=C) r.leftSource *
    (if R.kernelStatic he hprime u then
      (HistoryPairKernelProductReplacement.rightRootSupportIndicator (R.blockReference he) (fun _=>C.giant) y:ℂ)*
        (HistoryBulkPrincipalKernelReplacementMatched.sampledJacobian (R.blockReference he) z:ℂ)*
        (principalData R he (bulkSize k L/2) hout hprime hV).value true true u *
        (R.restoredKernelProduct (l:=l) he symbolic u:ℂ)
    else 0)

end CorrectedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
