import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementKernelDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainBulkDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainGiantDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainInitial
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainJoinFinite
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementProbabilityKernel
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementSquareDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryActualComparisonDecayArithmetic
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem plain_total_of_stage_bounds
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (D : PlainStageData C spectator l) (hl : l ≤ k)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) (mixed : Bool)
    (H : ℝ) (hm : 1 ≤ (bulkSize k L : ℝ))
    (h0 : ‖@plainOriginalAverage d Bs BD Bz L k l E C spectator σ mixed-
        @plainGiantAverage d Bs BD Bz L k l E C spectator D.reference hl σ mixed‖ ≤ Real.exp (-frequencyBudget Bs BD Bz k L l-(H+5)*(bulkSize k L:ℝ)) ∧
      ‖@plainOriginalAverage d Bs BD Bz L k l E C spectator σ mixed-
        @plainGiantAverage d Bs BD Bz L k l E C spectator D.reference hl σ mixed‖ ≤ Real.exp (-(H+5)*(bulkSize k L:ℝ)))
    (h1 : ‖@plainSquareAverage d Bs BD Bz L k l E C spectator D hl σ mixed false-
        @plainSquareAverage d Bs BD Bz L k l E C spectator D hl σ mixed true‖ ≤ Real.exp (-frequencyBudget Bs BD Bz k L l-(H+5)*(bulkSize k L:ℝ)) ∧
      ‖@plainSquareAverage d Bs BD Bz L k l E C spectator D hl σ mixed false-
        @plainSquareAverage d Bs BD Bz L k l E C spectator D hl σ mixed true‖ ≤ Real.exp (-(H+5)*(bulkSize k L:ℝ)))
    (h2 : ‖@plainKernelAverage d Bs BD Bz L k l E C spectator D hl σ mixed false-
        @plainKernelAverage d Bs BD Bz L k l E C spectator D hl σ mixed true‖ ≤ Real.exp (-frequencyBudget Bs BD Bz k L l-(H+5)*(bulkSize k L:ℝ)) ∧
      ‖@plainKernelAverage d Bs BD Bz L k l E C spectator D hl σ mixed false-
        @plainKernelAverage d Bs BD Bz L k l E C spectator D hl σ mixed true‖ ≤ Real.exp (-(H+5)*(bulkSize k L:ℝ)))
    (h3 : ‖@plainKernelAverage d Bs BD Bz L k l E C spectator D hl σ mixed true-
        @plainBulkAverage d Bs BD Bz L k l E C spectator D.reference hl σ mixed D.residues‖ ≤ Real.exp (-frequencyBudget Bs BD Bz k L l-(H+5)*(bulkSize k L:ℝ)) ∧
      ‖@plainKernelAverage d Bs BD Bz L k l E C spectator D hl σ mixed true-
        @plainBulkAverage d Bs BD Bz L k l E C spectator D.reference hl σ mixed D.residues‖ ≤ Real.exp (-(H+5)*(bulkSize k L:ℝ)))
    (h4 : ‖@plainBulkAverage d Bs BD Bz L k l E C spectator D.reference hl σ mixed D.residues-
        @plainFinalAverage d Bs BD Bz L k l E C spectator D.reference hl σ mixed D.residues‖ ≤ Real.exp (-frequencyBudget Bs BD Bz k L l-(H+5)*(bulkSize k L:ℝ)) ∧
      ‖@plainBulkAverage d Bs BD Bz L k l E C spectator D.reference hl σ mixed D.residues-
        @plainFinalAverage d Bs BD Bz L k l E C spectator D.reference hl σ mixed D.residues‖ ≤ Real.exp (-(H+5)*(bulkSize k L:ℝ)))
    : ‖@plainOriginalAverage d Bs BD Bz L k l E C spectator σ mixed-
        @plainFinalAverage d Bs BD Bz L k l E C spectator D.reference hl σ mixed D.residues‖ ≤ Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      ‖@plainOriginalAverage d Bs BD Bz L k l E C spectator σ mixed-
        @plainFinalAverage d Bs BD Bz L k l E C spectator D.reference hl σ mixed D.residues‖ ≤ Real.exp (-H*(bulkSize k L:ℝ)) :=
  @five_stage_bounds_of_eq (frequencyBudget Bs BD Bz k L l) H (bulkSize k L:ℝ) hm
    (@plainOriginalAverage d Bs BD Bz L k l E C spectator σ mixed)
    (@plainGiantAverage d Bs BD Bz L k l E C spectator D.reference hl σ mixed)
    (@plainSquareAverage d Bs BD Bz L k l E C spectator D hl σ mixed false)
    (@plainSquareAverage d Bs BD Bz L k l E C spectator D hl σ mixed true)
    (@plainKernelAverage d Bs BD Bz L k l E C spectator D hl σ mixed false)
    (@plainKernelAverage d Bs BD Bz L k l E C spectator D hl σ mixed true)
    (@plainBulkAverage d Bs BD Bz L k l E C spectator D.reference hl σ mixed D.residues)
    (@plainFinalAverage d Bs BD Bz L k l E C spectator D.reference hl σ mixed D.residues)
    (@plainGiantAverage_eq_plainSquareAverage d Bs BD Bz L k l E C spectator D hl σ mixed)
    (@plainSquareAverage_probability_eq_kernel d Bs BD Bz L k l E C spectator D hl σ mixed)
    h0 h1 h2 h3 h4

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
