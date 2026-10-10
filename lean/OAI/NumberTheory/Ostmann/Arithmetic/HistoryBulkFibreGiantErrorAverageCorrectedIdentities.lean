import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkDiagonalCorrectedSourceFibreReindex
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageBudgetDraws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageCorrectedActual

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage
open Construction Conclusion HistoryBulkSourceDisintegration HistoryGiantReferenceMean
open HistoryBulkFibreOriginalReference HistoryBulkFibreGiantApproximation
open HistoryBulkActualRootReferenceFamily (leftChoices rightChoices)
open HistoryBulkIndependentFibreReference
open HistoryBulkDiagonalCorrectedSourceFibreReindex
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)

theorem selectedDiagonalCovariance_eq_originalSourceAverage
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
    (he : PreservesRemainingBands _ e) :
    C.selectedDiagonalCovariance spectator (bulkSize k L/2) C.scale l e =
      originalSourceAverage C spectator (correctedOriginalValue C spectator e) := by
  rw [selectedDiagonalCovariance_eq_fibres]
  unfold correctedFibreMeanComplex
  simp only [guardedFibreMean,ite_eq_left he]
  simp_rw [root_choices_sum_eq_source_cmean]
  rfl

theorem selectedDiagonalCovariance_eq_guardedOriginalSourceAverage
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l)) :
    C.selectedDiagonalCovariance spectator (bulkSize k L/2) C.scale l e =
      if PreservesRemainingBands _ e then
        originalSourceAverage C spectator (correctedOriginalValue C spectator e) else 0 := by
  classical
  by_cases he : PreservesRemainingBands _ e
  · rw [ite_eq_left he]
    exact selectedDiagonalCovariance_eq_originalSourceAverage C spectator e he
  · rw [ite_eq_right he,selectedDiagonalCovariance_eq_fibres]
    simp only [correctedFibreMeanComplex,guardedFibreMean,ite_eq_right he,
      HistoryGiantOriginalMeanFactorization.choicesPairSum,FinitePrior.cmean,
      mul_zero,Finset.sum_const_zero]

end Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage

end

end OAI
