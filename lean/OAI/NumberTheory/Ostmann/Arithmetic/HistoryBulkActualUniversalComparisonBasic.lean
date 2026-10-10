import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementOriginalDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageIdentities
import OAI.NumberTheory.Ostmann.Conclusion.HistorySelectedCovarianceCauchy
import OAI.NumberTheory.Ostmann.Conclusion.SelectedCovarianceComplex
import OAI.NumberTheory.Ostmann.Construction.DiagonalSingleEnergy

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalComparison
open Construction Conclusion HistoryBulkActualTotalReplacement
open HistoryBulkFibreGiantErrorAverage
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)

theorem singleEnergy_le_norm_plainOriginal :
    C.selectedDiagonalSingleEnergy spectator (bulkSize k L/2) C.scale l ≤
      ‖plainOriginalAverage C spectator (l:=l) (Equiv.refl _) true‖ := by
  rw [selectedDiagonalSingleEnergy_eq_originalSourceAverage]
  exact (le_abs_self _).trans (Complex.abs_re_le_norm _)

theorem covariance_le_norm_plainOriginal
    (σ τ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2)))) :
    selectedCovariance C spectator (bulkSize k L/2) l σ τ ≤
      ‖plainOriginalAverage C spectator (l:=l) (Equiv.refl _) false‖ := by
  apply (selectedCovariance_le_identity C spectator (bulkSize k L/2) l σ τ).trans
  apply selectedCovariance_le_of_complex_norm
  rw [selectedComplexCovariance_eq_originalSourceAverage,inv_one,mul_one]
  change ‖originalSourceAverage C spectator (primeOriginalValue C spectator (Equiv.refl _))‖ ≤
    ‖originalSourceAverage C spectator (primeOriginalValue C spectator (Equiv.refl _))‖
  exact le_rfl

end Ostmann.Arithmetic.HistoryBulkActualUniversalComparison

end

end OAI
