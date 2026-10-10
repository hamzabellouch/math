import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedCoordinatesProduct
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedRestored

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

theorem restoredKernelProduct_eq (symbolic : Bool) (u : SelectedBulkSample C l) :
    R.restoredKernelProduct (l:=l) he symbolic u=R.kernelProduct (l:=l) he hprime symbolic u := by
  cases symbolic
  · change (∏q,actualProbability true (R.blockReference he).left.history (R.blockReference he).right.history
      (R.blockReference he).left.supported (R.blockReference he).right.supported q
      ((HistoryBulkPrincipalKernelReplacementMatched.referenceSample (R.blockReference he)
        (restoreOriginalDraw C l p o u)
        (HistoryPairRepresentativeVariables.representativeMap (R.blockReference he).left.history (R.blockReference he).right.history q)).toNat)
      (HistoryBulkPrincipalKernelReplacementMatched.referenceSample (R.blockReference he)
        (restoreOriginalDraw C l p o u)))=_
    exact (R.probabilityProduct_eq_restored_referenceSample (l:=l) he hprime true u).symm
  · simp only [restoredKernelProduct,kernelProduct,ite_true,
      R.restored_referenceSample_representative (l:=l) he u,Int.toNat_natCast]

end CorrectedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
