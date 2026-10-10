import OAI.NumberTheory.Ostmann.Arithmetic.CorrectedAggregatePoint
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedAggregateAlgebra

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

section
noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyCorrected
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkFibreGiantApproximation HistoryRepresentativeSourceSeparation
open HistoryBulkIndependentFibreReference HistoryBulkUniversalPatternAggregation
open HistoryBulkActualPrincipalKernelStageCorrected
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands (Template.remainder (l+1)
      (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) e) (hp : ∀q∈outside,q.Prime)
  (hAd : ∀r : Frame (l:=l) C outside, PairAdmissible r.left r.right outside)
  (hout : outside.length=2*(bulkSize k L/2))
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))

private theorem background_probability_rootExpression_eq_kernel_sum_core :
    (backgroundPrior C l).cmean (fun bg =>
      (selectedBulkPrior C l).cmean (fun sample =>
        rootExpression (l:=l) C outside e he hp hAd hout hV bg sample true)) =
    ∑ index : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
      ∑ pattern : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
        selectedKernelMean (l:=l) C pattern outside e he hout hp hV
          index.1 index.2.1 index.2.2 false :=
  (Eq.refl ((backgroundPrior C l).cmean (fun bg =>
    (selectedBulkPrior C l).cmean (fun u =>
      rootExpression (l:=l) C outside e he hp hAd hout hV bg u true)))).trans
    ((cmean_cmean_sum (backgroundPrior C l) (selectedBulkPrior C l)
      (fun bg u (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)) =>
        expression (l:=l) C outside e he hp hAd hout hV bg u i true)).trans
      (Finset.sum_congr rfl (fun i _ =>
        background_probability_expression_eq_kernel_mean
          (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
          C outside e he hp hAd hout hV i)))

public theorem background_probability_rootExpression_eq_kernel_sum :
    (backgroundPrior C l).cmean (fun bg =>
      (selectedBulkPrior C l).cmean (fun sample =>
        rootExpression (l:=l) C outside e he hp hAd hout hV bg sample true)) =
    ∑ index : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),
      ∑ pattern : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
        selectedKernelMean (l:=l) C pattern outside e he hout hp hV
          index.1 index.2.1 index.2.2 false :=
  background_probability_rootExpression_eq_kernel_sum_core
    (d:=d) (Bs:=Bs) (BD:=BD) (Bz:=Bz) (L:=L) (k:=k) (l:=l) (E:=E)
    C outside e he hp hAd hout hV

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyCorrected
end
end

end OAI
