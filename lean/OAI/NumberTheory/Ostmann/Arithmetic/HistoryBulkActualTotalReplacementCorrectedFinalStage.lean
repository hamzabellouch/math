import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualIntegralReplacementCorrected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedFinalStageBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedFinalStageStatement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion Filter HistoryBulkSourceDisintegration
open HistoryBulkActualIntegralReplacement HistoryBulkActualGoodPrincipal
open HistoryBulkIndependentFibreReference
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem selected_corrected_final_stage_eventually (d : Decomposition) (Bs BD Bz H : ℝ)
    {k : ℕ} (hBs : 0 ≤ Bs) (hH : 0 ≤ H) (hk : 2 ≤ k) :
    CorrectedFinalStageEstimate d Bs BD Bz H k :=
  (selected_corrected_bulk_error_eventually d Bs BD Bz H hBs hH hk).mono
    (fun L h E C hG hGu hcl hcu hb hd spectator hspec l hl hV e =>
      corrected_final_stage_average_bound C spectator hl e hV
        (Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)))
        (Real.exp (-H*(bulkSize k L:ℝ))) (Real.exp_nonneg _) (Real.exp_nonneg _)
        (fun he ds => (h E C hG hGu hcl hcu hb hd spectator hspec ds l hl).choose_spec e he))

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
