import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalCorrectedSourceSupport
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedCoordinatesProduct
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedNormalizeBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedProduct

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
local instance correctedNormalizeInternalDecidable (seed : List SourceSlot) (j : ℕ) : DecidableEq (Internal seed j) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {outside : List ℕ} {e : RemainingPermutation (k:=k) (L:=L) (l:=l)}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}
namespace CorrectedSelectedOuter
variable (R : CorrectedSelectedOuter (l:=l) C p o outside e i)
  (he : PreservesRemainingBands (Template.remainder (l+1)
    (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) e)
  (hout : outside.length=2*(bulkSize k L/2)) (hprime : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

theorem restoredKernelTerm_eq_jacobian_mul
    (symbolic : Bool) (u : SelectedBulkSample C l)
    (hm : originalDrawMass (fun _=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p (restoreOriginalDraw C l p o u)≠0) :
    R.restoredKernelTerm (l:=l) he hout hprime hV symbolic u =
      (∏q : Block p,((outerBlocks C l p o q).val:ℂ))*
        R.kernelTerm (l:=l) he hout hprime hV symbolic u := by
  have hs1 := R.rightRootSupportIndicator_eq_one (l:=l) he (restoreOriginalDraw C l p o u)
    (originalDrawOuter_restore C l p o u) hm
  have hj := R.restored_sampledJacobian_eq (l:=l) he u
  have hk := R.restoredKernelProduct_eq (l:=l) he hprime symbolic u
  exact normalize_guard_product_of_equalities (R.kernelStatic he hprime u)
    (Frame.extractedDensity (C:=C) (R.frame he hprime).leftSource)
    ((principalData R he (bulkSize k L/2) hout hprime hV).value true true u)
    (HistoryBulkPrincipalKernelReplacementMatched.sampledJacobian (C:=C) (l:=l) (R.blockReference he)
      (HistoryBulkPrincipalKernelReplacementMatched.referenceSample (C:=C) (l:=l) (R.blockReference he)
        (restoreOriginalDraw C l p o u)):ℂ)
    (R.restoredKernelProduct (l:=l) he symbolic u:ℂ)
    (HistoryPairKernelProductReplacement.rightRootSupportIndicator (R.blockReference he)
      (fun _=>C.giant) (restoreOriginalDraw C l p o u):ℂ)
    (∏q : Block p,((outerBlocks C l p o q).val:ℂ)) (R.kernelProduct he hprime symbolic u:ℂ)
    (congrArg (fun z : ℝ => (z:ℂ)) hs1)
    ((congrArg (fun z : ℝ => (z:ℂ)) hj).trans (by simp only [Complex.ofReal_prod,Complex.ofReal_natCast]))
    (congrArg (fun z : ℝ => (z:ℂ)) hk)

end CorrectedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
