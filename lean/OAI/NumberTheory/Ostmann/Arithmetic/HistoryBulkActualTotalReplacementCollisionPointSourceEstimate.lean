import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionPlainEstimate
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionPointSourceErrorConversion
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionPointSourceErrorStatement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Filter HistoryBulkActualPrincipalCollision

theorem selected_plain_collision_source_eventually (d : Decomposition) (Bs BD Bz H : ℝ)
    {k : ℕ} (hBs : 0 ≤ Bs) (hH : 0 ≤ H) (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop, PlainCollisionSourceError d Bs BD Bz H k L := by
  exact (selected_plainCollisionPrincipal_error_eventually d Bs BD Bz H hBs hH hk).mono
    (fun L h => plainCollisionErrorProperty_to_source d Bs BD Bz H k L h)

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
