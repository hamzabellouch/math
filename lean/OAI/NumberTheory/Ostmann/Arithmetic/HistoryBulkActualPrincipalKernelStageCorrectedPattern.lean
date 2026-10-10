import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedPatternAlgebra
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedPatternStatement

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
open HistoryBulkUniversalPatternAggregation
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (outside : List ℕ) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands (Template.remainder (l+1)
      (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) e)
  (hlen : outside.length=2*(bulkSize k L/2)) (hprime : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l)
  (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l)

theorem sum_selectedKernelMean_eq_background (symbolic : Bool) :
    PatternMeanEquality (l:=l) C outside e he hlen hprime hV v f g symbolic :=
  sum_eq_of_pointwise
    (fun p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l) =>
      selectedKernelMean (l:=l) C p outside e he hlen hprime hV v f g symbolic)
    (fun p => ∑o,(outerMass C l p o:ℂ)*(∏q : Block p,((outerBlocks C l p o q).val:ℂ))*
      (selectedBulkPrior C l).cmean (fun u=>
        selectedKernelOptionValue (l:=l) C p outside e he hlen hprime hV v f g o symbolic u))
    _
    (fun p => selectedKernelMean_eq_outerOption (l:=l) C p outside e he hlen hprime hV v f g symbolic)
    (HistoryBulkActualPrincipalKernelStage.typed_kernel_fubini C
      (fun p o u=>selectedKernelOptionValue (l:=l) C p outside e he hlen hprime hV v f g o symbolic u)
      (fun p o u=>selectedKernelOptionValue_typed (l:=l) C p outside e he hlen hprime hV v f g o symbolic u))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end

end OAI
