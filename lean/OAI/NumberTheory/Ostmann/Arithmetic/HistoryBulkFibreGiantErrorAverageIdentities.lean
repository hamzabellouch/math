import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkDiagonalSourceFibreReindex
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageBudgetDraws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageSourceMean
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferenceCovariance

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage
open Construction Conclusion HistoryBulkSourceDisintegration HistoryGiantReferenceMean
open HistoryBulkFibreOriginalReference HistoryBulkFibreGiantApproximation
open HistoryBulkActualRootReferenceFamily HistoryBulkDiagonalSourceFibreReindex
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)

theorem selectedComplexCovariance_eq_originalSourceAverage
    (σ τ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2)))) :
    selectedComplexCovariance C spectator (bulkSize k L/2) l σ τ =
      originalSourceAverage C spectator (primeOriginalValue C spectator (σ⁻¹*τ)) := by
  rw [selectedComplexCovariance_eq_fibres]
  simp_rw [root_choices_sum_eq_source_cmean]
  simp only [originalSourceAverage,primeOriginalValue,wholeMean,
    primeFibreMean_eq_weighted,weightedFibreTerm_eq_mul,one_mul,leftChoices,rightChoices]

theorem selectedDiagonalSingleEnergy_eq_originalSourceAverage :
    C.selectedDiagonalSingleEnergy spectator (bulkSize k L/2) C.scale l =
      (originalSourceAverage C spectator (mixedOriginalValue (l:=l) C spectator (Equiv.refl _))).re := by
  rw [selectedDiagonalSingleEnergy_eq_fibres]
  unfold diagonalFibreMeanComplex
  simp_rw [root_choices_sum_eq_source_cmean]
  simp only [originalSourceAverage,mixedOriginalValue,wholeMean,
    weightedMixedFibreMean_eq_weighted,leftChoices,rightChoices]
  rfl

end Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage

end

end OAI
