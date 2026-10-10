import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelPointStatement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelStageBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelStageStatement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion Filter HistoryBulkSourceDisintegration
open HistoryBulkIndependentFibreReference
attribute [local instance] Classical.propDecidable

theorem correctedKernelPointEstimate_to_stage (d : Decomposition) (Bs BD Bz H : ℝ) (k : ℕ)
    (h : SelectedCorrectedKernelPointEstimate d Bs BD Bz H k) :
    SelectedCorrectedKernelStageEstimate d Bs BD Bz H k :=
  h.mono
    (fun L h E C hG hGu hcl hcu hb hd spectator hspec l hl D e =>
      corrected_kernel_stage_average_bound C spectator D hl e
        (Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)))
        (Real.exp (-H*(bulkSize k L:ℝ))) (Real.exp_nonneg _) (Real.exp_nonneg _)
        (fun he ds => h E C hG hGu hcl hcu hb hd spectator hspec l hl D e he ds))

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
