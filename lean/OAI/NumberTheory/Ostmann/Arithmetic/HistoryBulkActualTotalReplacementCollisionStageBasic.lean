import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionPointStatement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionStageValueMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCollisionStatement
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementMean

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkSourceDisintegration
open scoped BigOperators
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem plain_collision_stage_average_bound
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (D : PlainStageData C spectator l) (hl : l≤k)
    (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2)))) (mixed : Bool)
    (r₁ r₂ : ℝ)
    (h : ∀ds : Fin (2*(bulkSize k L/2))→spectator.Sample,
      (∀i,spectator.law.mass (ds i)≠0) →
      ‖plainKernelValue C spectator D hl σ mixed true ds-
        plainCollisionBulkValue C spectator D hl σ mixed ds‖≤r₁ ∧
      ‖plainKernelValue C spectator D hl σ mixed true ds-
        plainCollisionBulkValue C spectator D hl σ mixed ds‖≤r₂) :
    ‖plainKernelAverage C spectator D hl σ mixed true-
      plainBulkAverage C spectator D.reference hl σ mixed D.residues‖≤r₁ ∧
    ‖plainKernelAverage C spectator D hl σ mixed true-
      plainBulkAverage C spectator D.reference hl σ mixed D.residues‖≤r₂ :=
  let hmean := norm_cmean_sub_le_both (spectatorPrior spectator (2*(bulkSize k L/2)))
    (plainKernelValue C spectator D hl σ mixed true)
    (fun ds=>plainCollisionBulkValue C spectator D hl σ mixed ds)
    r₁ r₂ (fun ds hds=>h ds
      (fun i=>Finset.prod_ne_zero_iff.mp
        (show (∏j,spectator.law.mass (ds j))≠0 from hds) i (Finset.mem_univ i)))
  let heq := congrArg (fun z : ℂ=>‖plainKernelAverage C spectator D hl σ mixed true-z‖)
    (plainBulkAverage_eq_collisionBulkValue_mean C spectator D hl σ mixed)
  ⟨heq.trans_le hmean.1,heq.trans_le hmean.2⟩

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
