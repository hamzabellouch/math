import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageSelectedCorrectedIndexStatement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelPointFinite
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelPointStatement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion Filter HistoryBulkSourceDisintegration
open HistoryBulkActualPrincipalKernelStageCorrected
open HistoryBulkIndependentFibreReference

theorem correctedKernelIndexEstimate_to_point (d : Decomposition) (Bs BD Bz H : ℝ) (k : ℕ)
    (h : SelectedKernelIndexEstimate d Bs BD Bz H k) :
    SelectedCorrectedKernelPointEstimate d Bs BD Bz H k :=
  h.mono
    (fun L hL E C hG hGu hcl hcu hb hd spectator hspec l hl D e he ds =>
      (hL E C hG hGu hcl hcu hb hd spectator hspec
        (spectatorList spectator ds)
        (fun _q hq => (List.mem_ofFn.mp hq).elim (fun i hi => ⟨ds i,hi⟩))
        List.length_ofFn l hl e he).elim (fun hp hex => hex.elim (fun hV hbound =>
          correctedKernelValue_bounds C spectator D hl e he ds hp hV
            (Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)))
            (Real.exp (-H*(bulkSize k L:ℝ))) hbound)))

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
