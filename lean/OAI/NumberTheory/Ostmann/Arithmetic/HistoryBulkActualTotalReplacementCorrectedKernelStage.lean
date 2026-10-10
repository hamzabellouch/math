import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelPoint
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelStageConversion
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelStageStatement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

theorem selected_corrected_kernel_stage_eventually (d : Decomposition) (Bs BD Bz H : ℝ)
    {k : ℕ} (hBs : 0≤Bs) (hH : 0≤H) (hk : 0<k) :
    SelectedCorrectedKernelStageEstimate d Bs BD Bz H k :=
  correctedKernelPointEstimate_to_stage d Bs BD Bz H k
    (selected_corrected_kernel_point_eventually d Bs BD Bz H hBs hH hk)

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
