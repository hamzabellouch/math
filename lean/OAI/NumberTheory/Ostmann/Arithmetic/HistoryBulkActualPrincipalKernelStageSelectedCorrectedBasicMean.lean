import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedMeanScalarDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
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
  (he : PreservesRemainingBands _ e)
  (hlen : outside.length=2*(bulkSize k L/2)) (hprime : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
  (v : AllowedFrequency (frequencyBound Bs BD Bz k L) l)
  (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l)

theorem selectedKernelMean_sub :
    selectedKernelMean (l:=l) C p outside e he hlen hprime hV v f g false -
      selectedKernelMean (l:=l) C p outside e he hlen hprime hV v f g true =
    densityPrincipalDifferenceMean
      (correctedPrincipalFamily (l:=l) C p outside e he (bulkSize k L/2) hlen hprime hV v f g)
      (correctedDensitySources (l:=l) C outside e he (bulkSize k L/2) hlen hprime hV p v f g)
      true true (selectedKernelMask (l:=l) C p outside e he hprime v f g) :=
  (congrArg₂ (fun a b : ℂ => a-b)
    (selectedKernelMean.eq_def C p outside e he hlen hprime hV v f g false)
    (selectedKernelMean.eq_def C p outside e he hlen hprime hV v f g true)).trans
    (densityPrincipalProductMean_sub
      (correctedPrincipalFamily (l:=l) C p outside e he (bulkSize k L/2) hlen hprime hV v f g)
      (correctedDensitySources (l:=l) C outside e he (bulkSize k L/2) hlen hprime hV p v f g)
      true true (selectedKernelMask (l:=l) C p outside e he hprime v f g))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end

end OAI
