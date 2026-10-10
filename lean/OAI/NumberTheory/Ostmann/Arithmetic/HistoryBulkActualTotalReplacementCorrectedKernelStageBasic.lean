import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelFinite

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkIndependentFibreReference
attribute [local instance] Classical.propDecidable
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem corrected_kernel_stage_average_bound
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (D : PlainStageData C spectator l) (hl : l<k)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
    (r₁ r₂ : ℝ) (hr₁ : 0≤r₁) (hr₂ : 0≤r₂)
    (h : ∀he : PreservesRemainingBands _ e,∀ds,
      ‖correctedKernelValue C spectator D hl e he false ds-
        correctedKernelValue C spectator D hl e he true ds‖≤r₁ ∧
      ‖correctedKernelValue C spectator D hl e he false ds-
        correctedKernelValue C spectator D hl e he true ds‖≤r₂) :
    ‖correctedKernelAverage C spectator D hl e false-
      correctedKernelAverage C spectator D hl e true‖≤r₁ ∧
    ‖correctedKernelAverage C spectator D hl e false-
      correctedKernelAverage C spectator D hl e true‖≤r₂ :=
  norm_guarded_cmean_sub_le_both (spectatorPrior spectator (2*(bulkSize k L/2)))
    (PreservesRemainingBands _ e)
    (fun he => correctedKernelValue C spectator D hl e he false)
    (fun he => correctedKernelValue C spectator D hl e he true)
    r₁ r₂ hr₁ hr₂ (fun he ds _ => h he ds)

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
