import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualIntegralReplacementPlain
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainFinalStageBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainFinalStageStatement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion Filter HistoryBulkSourceDisintegration
open HistoryBulkActualIntegralReplacement HistoryBulkActualGoodPrincipal
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem selected_plain_final_stage_eventually (d : Decomposition) (Bs BD Bz H : ℝ)
    {k : ℕ} (hBs : 0 ≤ Bs) (hH : 0 ≤ H) (hk : 2 ≤ k) :
    PlainFinalStageEstimate d Bs BD Bz H k :=
  (selected_plain_bulk_error_eventually d Bs BD Bz H hBs hH hk).mono
    (fun L h E C hG hGu hcl hcu hb hd spectator hspec =>
      (h E C hG hGu hcl hcu hb hd spectator hspec).elim fun _ hpoint =>
      fun hactual l hl hV σ mixed =>
        plain_final_stage_average_bound C spectator hactual hl σ mixed hV
          (Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)))
          (Real.exp (-H*(bulkSize k L:ℝ)))
          (fun ds => (hpoint ds l hl).choose_spec σ mixed))

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
