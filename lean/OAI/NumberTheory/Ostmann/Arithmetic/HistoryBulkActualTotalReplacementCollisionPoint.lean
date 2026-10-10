import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionPointConversion
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionPointSourceEstimate
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionPointStatement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Filter

theorem selected_plain_collision_point_eventually (d : Decomposition) (Bs BD Bz H : ℝ)
    {k : ℕ} (hBs : 0 ≤ Bs) (hH : 0 ≤ H) (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop, PlainCollisionPoint d Bs BD Bz H k L := by
  exact (selected_plain_collision_source_eventually d Bs BD Bz H hBs hH hk).mono
    (fun L h => plainCollisionSourceError_to_point d Bs BD Bz H k L h)

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
