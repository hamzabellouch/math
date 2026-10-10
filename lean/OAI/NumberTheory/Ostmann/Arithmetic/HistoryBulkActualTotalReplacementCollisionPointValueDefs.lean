import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionPointSourceValueDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementStageData

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

def plainCollisionBulkValue (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (D : PlainStageData C spectator l) (hl : l ≤ k)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) (mixed : Bool)
    (ds : Fin (2*(bulkSize k L/2)) → spectator.Sample) : ℂ :=
  plainCollisionSourceBulkValue C spectator ds D.reference hl σ mixed (D.residues ds)

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
