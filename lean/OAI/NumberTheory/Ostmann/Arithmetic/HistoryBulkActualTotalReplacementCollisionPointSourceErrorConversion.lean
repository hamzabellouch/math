import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionKernelStagePlainCollisionIdentity
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionPlainErrorProperty
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionPlainSupport
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionPointSourceErrorStatement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionPointSourceFalse

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkActualPrincipalCollision

theorem plainCollisionErrorProperty_to_source (d : Decomposition) (Bs BD Bz H : ℝ)
    (k : ℕ) (L : ℝ) (h : plainErrorProperty d Bs BD Bz H k L) :
    PlainCollisionSourceError d Bs BD Bz H k L := by
  intro E C hG hGu hcl hcu hb hd spectator hspec hactual ds hds l hl σ mixed hV
  exact error_bounds_of_eq
    (plainKernelCollisionSourceValue_eq_plainCollisionPrincipal C spectator ds hactual hl σ mixed hV)
    (plainCollisionSourceBulkValue_eq_false C spectator ds hactual hl σ mixed hV)
    (h E C hG hGu hcl hcu hb hd spectator hspec hactual ds hds l hl σ mixed hV)

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
