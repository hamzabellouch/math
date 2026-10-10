import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedBulkDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedInitial
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedKernelDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedProbabilityKernel
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedSquareDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainJoinFinite
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageCorrectedScalarDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkFibreGiantErrorAverage HistoryBulkIndependentFibreReference
open HistoryActualComparisonDecayArithmetic
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem corrected_total_of_stage_bounds
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (D : PlainStageData C spectator l) (hl : l < k)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
    (H : ℝ) (hm : 1 ≤ (bulkSize k L : ℝ))
    (h0 : ‖@InitialSourceChoice.selectedDiagonalCovariance d Bs BD Bz k L E C spectator (bulkSize k L/2) C.scale l e-
        @correctedGuardedPrincipalAverage d Bs BD Bz L k l E C spectator e‖ ≤ Real.exp (-frequencyBudget Bs BD Bz k L l-(H+5)*(bulkSize k L:ℝ)) ∧
      ‖@InitialSourceChoice.selectedDiagonalCovariance d Bs BD Bz k L E C spectator (bulkSize k L/2) C.scale l e-
        @correctedGuardedPrincipalAverage d Bs BD Bz L k l E C spectator e‖ ≤ Real.exp (-(H+5)*(bulkSize k L:ℝ)))
    (h1 : ‖@correctedSquareAverage d Bs BD Bz L k l E C spectator D hl e false-
        @correctedSquareAverage d Bs BD Bz L k l E C spectator D hl e true‖ ≤ Real.exp (-frequencyBudget Bs BD Bz k L l-(H+5)*(bulkSize k L:ℝ)) ∧
      ‖@correctedSquareAverage d Bs BD Bz L k l E C spectator D hl e false-
        @correctedSquareAverage d Bs BD Bz L k l E C spectator D hl e true‖ ≤ Real.exp (-(H+5)*(bulkSize k L:ℝ)))
    (h2 : ‖@correctedKernelAverage d Bs BD Bz L k l E C spectator D hl e false-
        @correctedKernelAverage d Bs BD Bz L k l E C spectator D hl e true‖ ≤ Real.exp (-frequencyBudget Bs BD Bz k L l-(H+5)*(bulkSize k L:ℝ)) ∧
      ‖@correctedKernelAverage d Bs BD Bz L k l E C spectator D hl e false-
        @correctedKernelAverage d Bs BD Bz L k l E C spectator D hl e true‖ ≤ Real.exp (-(H+5)*(bulkSize k L:ℝ)))
    (h3 : ‖@correctedKernelAverage d Bs BD Bz L k l E C spectator D hl e true-
        @correctedBulkAverage d Bs BD Bz L k l E C spectator hl e D.residues‖ ≤ Real.exp (-frequencyBudget Bs BD Bz k L l-(H+5)*(bulkSize k L:ℝ)) ∧
      ‖@correctedKernelAverage d Bs BD Bz L k l E C spectator D hl e true-
        @correctedBulkAverage d Bs BD Bz L k l E C spectator hl e D.residues‖ ≤ Real.exp (-(H+5)*(bulkSize k L:ℝ)))
    (h4 : ‖@correctedBulkAverage d Bs BD Bz L k l E C spectator hl e D.residues-
        @correctedFinalAverage d Bs BD Bz L k l E C spectator hl e D.residues‖ ≤ Real.exp (-frequencyBudget Bs BD Bz k L l-(H+5)*(bulkSize k L:ℝ)) ∧
      ‖@correctedBulkAverage d Bs BD Bz L k l E C spectator hl e D.residues-
        @correctedFinalAverage d Bs BD Bz L k l E C spectator hl e D.residues‖ ≤ Real.exp (-(H+5)*(bulkSize k L:ℝ)))
    : ‖@InitialSourceChoice.selectedDiagonalCovariance d Bs BD Bz k L E C spectator (bulkSize k L/2) C.scale l e-
        @correctedFinalAverage d Bs BD Bz L k l E C spectator hl e D.residues‖ ≤ Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      ‖@InitialSourceChoice.selectedDiagonalCovariance d Bs BD Bz k L E C spectator (bulkSize k L/2) C.scale l e-
        @correctedFinalAverage d Bs BD Bz L k l E C spectator hl e D.residues‖ ≤ Real.exp (-H*(bulkSize k L:ℝ)) := by
  exact @five_stage_bounds_of_eq (frequencyBudget Bs BD Bz k L l) H (bulkSize k L:ℝ) hm
    (@InitialSourceChoice.selectedDiagonalCovariance d Bs BD Bz k L E C spectator (bulkSize k L/2) C.scale l e)
    (@correctedGuardedPrincipalAverage d Bs BD Bz L k l E C spectator e)
    (@correctedSquareAverage d Bs BD Bz L k l E C spectator D hl e false)
    (@correctedSquareAverage d Bs BD Bz L k l E C spectator D hl e true)
    (@correctedKernelAverage d Bs BD Bz L k l E C spectator D hl e false)
    (@correctedKernelAverage d Bs BD Bz L k l E C spectator D hl e true)
    (@correctedBulkAverage d Bs BD Bz L k l E C spectator hl e D.residues)
    (@correctedFinalAverage d Bs BD Bz L k l E C spectator hl e D.residues)
    (@correctedGuardedPrincipalAverage_eq_correctedSquareAverage d Bs BD Bz L k l E C spectator D hl e)
    (@correctedSquareAverage_probability_eq_kernel d Bs BD Bz L k l E C spectator D hl e)
    h0 h1 h2 h3 h4

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI
