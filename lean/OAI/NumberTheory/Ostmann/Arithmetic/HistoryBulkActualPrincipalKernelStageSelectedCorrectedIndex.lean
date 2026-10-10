import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageSelectedCorrected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageSelectedCorrectedIndexConversion
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageSelectedCorrectedIndexStatement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

theorem selected_kernel_index_errors_eventually (d : Decomposition)
    (Bs BD Bz H : ℝ) {k : ℕ} (hBs : 0 ≤ Bs) (hH : 0 ≤ H) (hk : 0 < k) :
    SelectedKernelIndexEstimate d Bs BD Bz H k :=
  selectedKernelSumEstimate_to_index d Bs BD Bz H k
    (selected_kernel_sum_errors_eventually d Bs BD Bz H hBs hH hk)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end

end OAI
