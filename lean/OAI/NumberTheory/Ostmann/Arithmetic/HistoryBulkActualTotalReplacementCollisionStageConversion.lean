import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionPointStatement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionStageBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionStatement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion Filter

theorem plainCollisionPoint_to_stage (d : Decomposition) (Bs BD Bz H : ℝ) (k : ℕ)
    (h : ∀ᶠL : ℝ in atTop,PlainCollisionPoint d Bs BD Bz H k L) :
    ∀ᶠL : ℝ in atTop,PlainCollisionStage d Bs BD Bz H k L :=
  h.mono (fun L h E C hG hGu hcl hcu hb hd spectator hspec l hl D σ mixed =>
    plain_collision_stage_average_bound C spectator D hl σ mixed
      (Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)))
      (Real.exp (-H*(bulkSize k L:ℝ)))
      (fun ds hds=>h E C hG hGu hcl hcu hb hd spectator hspec l hl D σ mixed ds hds))

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
