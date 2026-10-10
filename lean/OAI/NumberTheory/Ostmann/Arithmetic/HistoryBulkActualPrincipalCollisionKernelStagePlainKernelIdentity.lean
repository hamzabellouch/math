import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionKernelStagePlainKernelDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementKernelDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction Conclusion HistoryBulkActualTotalReplacement
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem plainKernelValue_eq_plainKernelSourceValue
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (D : PlainStageData C spectator l) (hl : l≤k)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) (mixed : Bool)
    (ds : Fin (2*(bulkSize k L/2)) → spectator.Sample) :
    plainKernelValue C spectator D hl σ mixed true ds =
      plainKernelSourceValue C spectator D.reference hl σ mixed ds (D.residues ds) := by
  unfold plainKernelSourceValue
  rfl

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
