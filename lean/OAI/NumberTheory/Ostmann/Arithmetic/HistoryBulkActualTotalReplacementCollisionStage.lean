import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionPoint
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionStageConversion
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionStatement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Conclusion Filter

theorem selected_plain_collision_stage_eventually
    (d : Decomposition) (Bs BD Bz H : ℝ) {k : ℕ}
    (hBs : 0≤Bs) (hH : 0≤H) (hk : 2≤k) :
    ∀ᶠL : ℝ in atTop,PlainCollisionStage d Bs BD Bz H k L :=
  plainCollisionPoint_to_stage d Bs BD Bz H k
    (selected_plain_collision_point_eventually d Bs BD Bz H hBs hH hk)

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
