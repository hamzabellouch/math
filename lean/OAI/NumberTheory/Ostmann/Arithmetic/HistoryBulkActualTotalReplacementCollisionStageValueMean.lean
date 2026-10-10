import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionPointValueDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionStageSourceMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainBulkDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem plainBulkAverage_eq_collisionBulkValue_mean
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (D : PlainStageData C spectator l) (hl : l≤k)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2)))) (mixed : Bool) :
    plainBulkAverage C spectator D.reference hl σ mixed D.residues =
      (spectatorPrior spectator (2*(bulkSize k L/2))).cmean
        (plainCollisionBulkValue C spectator D hl σ mixed) := by
  refine (plainBulkAverage_eq_sourceValue_mean C spectator D.reference hl σ mixed D.residues).trans ?_
  apply congrArg (spectatorPrior spectator (2*(bulkSize k L/2))).cmean
  funext ds
  unfold plainCollisionBulkValue
  rfl

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
