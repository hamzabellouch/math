import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageSelectedCorrectedBasicMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageSelectedFinite

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
open HistoryBulkActualPrincipalKernelStage
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (e : RemainingPermutation (k:=k) (L:=L) (l:=l)) (he : PreservesRemainingBands _ e)
  (hlen : outside.length=2*(bulkSize k L/2)) (hprime : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

theorem selectedKernelMean_zero_cost_bounds (r₁ r₂ : ℝ)
    (hb : Real.exp (0*(L+1)^2)*correctedDensityKernelError (l:=l)
      C outside e he (bulkSize k L/2) hlen hprime hV
      (fun v f g p => selectedKernelMask (l:=l) C p outside e he hprime v f g) ≤ r₁ ∧
      Real.exp (0*(L+1)^2)*correctedDensityKernelError (l:=l)
      C outside e he (bulkSize k L/2) hlen hprime hV
      (fun v f g p => selectedKernelMask (l:=l) C p outside e he hprime v f g) ≤ r₂) :
    ‖(∑v,∑f,∑g,∑p,selectedKernelMean (l:=l) C p outside e he hlen hprime hV v f g false)-
      (∑v,∑f,∑g,∑p,selectedKernelMean (l:=l) C p outside e he hlen hprime hV v f g true)‖ ≤ r₁ ∧
    ‖(∑v,∑f,∑g,∑p,selectedKernelMean (l:=l) C p outside e he hlen hprime hV v f g false)-
      (∑v,∑f,∑g,∑p,selectedKernelMean (l:=l) C p outside e he hlen hprime hV v f g true)‖ ≤ r₂ :=
  let F := fun v f g p => correctedPrincipalFamily (l:=l) C p outside e he
    (bulkSize k L/2) hlen hprime hV v f g
  let X := fun v f g p => correctedDensitySources (l:=l) C outside e he
    (bulkSize k L/2) hlen hprime hV p v f g
  let mask := fun v f g p => selectedKernelMask (l:=l) C p outside e he hprime v f g
  four_sum_zero_cost_bounds
    (fun v f g p => selectedKernelMean (l:=l) C p outside e he hlen hprime hV v f g false)
    (fun v f g p => selectedKernelMean (l:=l) C p outside e he hlen hprime hV v f g true)
    (fun v f g p => densityPrincipalDifferenceMean (F v f g p) (X v f g p) true true (mask v f g p))
    (fun v f g p => selectedKernelMean_sub C p outside e he hlen hprime hV v f g)
    L r₁ r₂ hb

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end

end OAI
