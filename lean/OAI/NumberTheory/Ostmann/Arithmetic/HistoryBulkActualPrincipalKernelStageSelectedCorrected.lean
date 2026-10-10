import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualCorrectedPrincipalBlockFamilyDensitySelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageSelectedCorrectedBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageSelectedCorrectedStatement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected
open Construction Conclusion HistoryBulkActualCorrectedPrincipalBlockFamily Filter

theorem selected_kernel_sum_errors_eventually (d : Decomposition)
    (Bs BD Bz H : ℝ) {k : ℕ} (hBs : 0 ≤ Bs) (hH : 0 ≤ H) (hk : 0 < k) :
    SelectedKernelSumEstimate d Bs BD Bz H k := by
  exact (selected_corrected_principal_factory_density_kernel_error_eventually
    d Bs BD Bz 0 H hBs hH hk).mono
    (fun L h E C hG hGu hcl hcu hb hd spectator hspec outside houtside hlen l hl e he =>
      (h E C hG hGu hcl hcu hb hd spectator hspec outside houtside
        (bulkSize k L/2) hlen (hlen.trans_le (Nat.mul_div_le (bulkSize k L) 2)) l hl e he).elim
        (fun hprime hex => hex.elim (fun hV hbound =>
          ⟨hprime,hV,selectedKernelMean_zero_cost_bounds (l:=l) C outside e he hlen hprime hV
            (Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)))
            (Real.exp (-H*(bulkSize k L:ℝ)))
            (hbound (fun v f g p => selectedKernelMask (l:=l) C p outside e he hprime v f g))⟩)))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end

end OAI
