import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageSelectedCorrectedIndexBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageSelectedCorrectedIndexStatement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected
open Construction Conclusion Filter

theorem selectedKernelSumEstimate_to_index (d : Decomposition)
    (Bs BD Bz H : ℝ) (k : ℕ)
    (h : SelectedKernelSumEstimate d Bs BD Bz H k) :
    SelectedKernelIndexEstimate d Bs BD Bz H k := by
  exact h.mono
    (fun L h E C hG hGu hcl hcu hb hd spectator hspec outside houtside hlen l hl e he =>
      (h E C hG hGu hcl hcu hb hd spectator hspec outside houtside hlen l hl e he).elim
        (fun hprime hex => hex.elim (fun hV hbound =>
          ⟨hprime,hV,selectedKernelMean_index_bounds (l:=l) C outside e he hlen hprime hV
            (Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)))
            (Real.exp (-H*(bulkSize k L:ℝ))) hbound⟩)))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end

end OAI
