import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterEquivBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterMass
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedMeanOption
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedMeanStatement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedTerm

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation HistoryBulkIndependentFibreReference
open HistoryBulkActualPrincipalBlockFamily HistoryBulkActualGoodPrincipal
open HistoryBulkActualCorrectedPrincipalBlockFamily HistoryBulkPrincipalKernelReplacementMatched
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (outside : List ℕ) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands (Template.remainder (l+1)
    (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) e)
  (hlen : outside.length=2*(bulkSize k L/2)) (hprime : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l)
  (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l)

theorem densityPrincipalProductTerm_eq_jacobian_option
    (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (symbolic : Bool) (u : SelectedBulkSample C l)
    (ho : outerMass C l p o≠0) (hu : (selectedBulkPrior C l).mass u≠0) :
    JacobianOptionEquality (l:=l) C p outside e he hlen hprime hV v f g o symbolic u :=
  (densityPrincipalProductTerm_eq_restoredOption (l:=l) C p outside e he hlen hprime hV v f g o symbolic u).trans
    (restoredOption_eq_jacobian_option (l:=l) C p outside e he hlen hprime hV v f g o symbolic u ho hu)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end

end OAI
