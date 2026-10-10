import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionKernelStagePlainCollisionDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionKernelStagePlainKernelIdentity
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalCollisionKernelStagePlainSource
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementKernelDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction Conclusion HistoryBulkActualTotalReplacement HistoryBulkSourceDisintegration
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
  (D : PlainStageData C spectator l) (hl : l≤k)
  (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))

theorem plainKernelValue_symbolic_eq_collisionSourceValue (mixed : Bool)
    (ds : Fin (2*(bulkSize k L/2))→spectator.Sample) :
    plainKernelValue C spectator D hl σ mixed true ds =
      plainKernelCollisionSourceValue C spectator ds D.reference hl σ mixed (D.residues ds) :=
  @Eq.trans ℂ _
    (plainKernelSourceValue C spectator D.reference hl σ mixed ds (D.residues ds)) _
    (plainKernelValue_eq_plainKernelSourceValue C spectator D hl σ mixed ds)
    (plainKernelSourceValue_eq_collisionSourceValue C spectator D.reference hl σ mixed ds (D.residues ds))

theorem plainKernelAverage_symbolic_eq_collisionSourceAverage (mixed : Bool) :
    plainKernelAverage C spectator D hl σ mixed true =
      (spectatorPrior spectator (2*(bulkSize k L/2))).cmean (fun ds=>
        plainKernelCollisionSourceValue C spectator ds D.reference hl σ mixed (D.residues ds)) :=
  FinitePrior.cmean_congr_support (spectatorPrior spectator (2*(bulkSize k L/2))) _ _
    (fun ds _=>plainKernelValue_symbolic_eq_collisionSourceValue C spectator D hl σ mixed ds)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
