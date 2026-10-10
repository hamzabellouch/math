import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedAmplitude
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReferenceSplice

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
  (he : PreservesRemainingBands (Template.remainder (l+1)
    (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) e)
  (hout : outside.length=2*(bulkSize k L/2)) (hprime : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

theorem squareReference_value_eq_principalData
    (had : HistoryRepresentativeSourceSeparation.PairAdmissible
      (R.frame (l:=l) he hprime).left (R.frame (l:=l) he hprime).right outside)
    (u : SelectedBulkSample C l) (hu : (selectedBulkPrior C l).mass u≠0) :
    (R.squareReference (l:=l) he hprime had hout hV u hu).principal.value true true
      (R.squareReference (l:=l) he hprime had hout hV u hu).newBulk =
      (principalData (l:=l) R he (bulkSize k L/2) hout hprime hV).value true true u := by
  rw [R.principalData_value_eq_frame (l:=l) he hout hprime hV u]
  exact HistoryBulkPrincipalBSquareReference.principalSquareReference_value_eq _ _ _ _ _ _ _ _ _ _ _ _

end CorrectedSelectedOuter
end Ostmann.Arithmetic.HistoryBulkActualGoodPrincipal

end

end OAI
