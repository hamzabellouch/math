import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageSelectedCorrectedIndex
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelPointConversion
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelPointStatement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion Filter HistoryBulkSourceDisintegration
open HistoryBulkActualPrincipalKernelStageCorrected
open HistoryBulkIndependentFibreReference

theorem selected_corrected_kernel_point_eventually (d : Decomposition) (Bs BD Bz H : ℝ)
    {k : ℕ} (hBs : 0≤Bs) (hH : 0≤H) (hk : 0<k) :
    SelectedCorrectedKernelPointEstimate d Bs BD Bz H k :=
  correctedKernelIndexEstimate_to_point d Bs BD Bz H k
    (selected_kernel_index_errors_eventually d Bs BD Bz H hBs hH hk)

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
