import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrectedMeanScalarDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageSelectedIndexFinite

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected
open Construction Conclusion HistoryBulkIndependentFibreReference
open HistoryBulkActualRootReferenceFamily Filter
open HistoryBulkActualPrincipalKernelStage
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  (e : RemainingPermutation (k:=k) (L:=L) (l:=l)) (he : PreservesRemainingBands _ e)
  (hlen : outside.length=2*(bulkSize k L/2)) (hprime : ∀q∈outside,q.Prime)
  (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)

theorem selectedKernelMean_index_bounds (r₁ r₂ : ℝ) :
    let F := fun symbolic v f g p =>
      selectedKernelMean (l:=l) C p outside e he hlen hprime hV v f g symbolic
    (‖(∑v,∑f,∑g,∑p,F false v f g p)-(∑v,∑f,∑g,∑p,F true v f g p)‖ ≤ r₁ ∧
      ‖(∑v,∑f,∑g,∑p,F false v f g p)-(∑v,∑f,∑g,∑p,F true v f g p)‖ ≤ r₂) →
    (‖(∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),∑p,F false i.1 i.2.1 i.2.2 p)-
      (∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),∑p,F true i.1 i.2.1 i.2.2 p)‖ ≤ r₁ ∧
    ‖(∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),∑p,F false i.1 i.2.1 i.2.2 p)-
      (∑i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l),∑p,F true i.1 i.2.1 i.2.2 p)‖ ≤ r₂) :=
  let F := fun symbolic v f g p =>
    selectedKernelMean (l:=l) C p outside e he hlen hprime hV v f g symbolic
  fun hb => four_sum_bounds_to_index (F false) (F true) r₁ r₂ hb

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end

end OAI
