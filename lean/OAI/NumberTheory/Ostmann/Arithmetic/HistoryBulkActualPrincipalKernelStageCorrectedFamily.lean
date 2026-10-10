import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedFamilySquare
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedOptionBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyCorrectedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyCorrectedFactors

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyCorrected
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkFibreGiantApproximation HistoryBulkFibreOriginalReference
open HistoryBulkPrincipalBSquareReplacement HistoryRepresentativeSourceSeparation
open HistoryBulkReferencePeriodicMeanSource HistoryBulkActualGoodPrincipal
open HistoryBulkIndependentFibreReference HistoryBulkActualPrincipalKernelStageCorrected
open HistoryBulkUniversalPatternAggregation
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
  (he : PreservesRemainingBands (Template.remainder (l+1)
    (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)) e)
  (hp : ∀q∈outside,q.Prime)
  (hAd : ∀r : Frame (l:=l) C outside, PairAdmissible r.left r.right outside)
  (hout : outside.length=2*(bulkSize k L/2))
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (bg : Background C l) (u : SelectedBulkSample C l)
  (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))

theorem expression_probability_eq_kernel_pattern
    (hu : (selectedBulkPrior C l).mass u≠0) :
    expression (l:=l) C outside e he hp hAd hout hV bg u i true =
      patternComplexSum C.sources
        (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
        (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
        (fun p b=>selectedKernelOptionValue (l:=l) C p outside e he hout hp hV
          i.1 i.2.1 i.2.2 (restoreOuterBackground C l p bg b) false u) := by
  unfold expression densityBExpressionSum
  apply congrArg (patternComplexSum C.sources _ _)
  funext p b
  rw [densityPatternFactor_eq]
  unfold selectedTerm selectedOuter selectedKernelOptionValue
  cases hr : selectCorrectedOuterReference (l:=l) C p
      (restoreOuterBackground C l p bg b) outside e i with
  | none => rfl
  | some R =>
    exact squareTerm_true_eq_kernelTerm (l:=l) C outside e he hp hAd hout hV bg u i p b R hu

theorem mean_expression_probability_eq_kernel_pattern :
    (selectedBulkPrior C l).cmean (fun u=>
      expression (l:=l) C outside e he hp hAd hout hV bg u i true) =
    (selectedBulkPrior C l).cmean (fun u=>
      patternComplexSum C.sources
        (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
        (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
        (fun p b=>selectedKernelOptionValue (l:=l) C p outside e he hout hp hV
          i.1 i.2.1 i.2.2 (restoreOuterBackground C l p bg b) false u)) := by
  apply FinitePrior.cmean_congr_support
  intro u hu
  exact expression_probability_eq_kernel_pattern (l:=l) C outside e he hp hAd hout hV bg u i hu

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexFamilyCorrected

end

end OAI
