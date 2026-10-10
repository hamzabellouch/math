import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionKernelStagePlain
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionPointSourceErrorStatement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionPointStatement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionPointValueIdentity

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkActualPrincipalCollision

theorem plainCollisionSourceError_to_point (d : Decomposition) (Bs BD Bz H : ℝ)
    (k : ℕ) (L : ℝ) (h : PlainCollisionSourceError d Bs BD Bz H k L) :
    PlainCollisionPoint d Bs BD Bz H k L := by
  intro E C hG hGu hcl hcu hb hd spectator hspec l hl D σ mixed ds hds
  dsimp only
  rw [plainCollisionBulkValue_eq_sourceValue C spectator D hl σ mixed ds,
    plainKernelValue_symbolic_eq_collisionSourceValue C spectator D hl σ mixed ds]
  exact h E C hG hGu hcl hcu hb hd spectator hspec D.reference ds hds l hl σ mixed (D.residues ds)

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
