import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementOriginalDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageIdentities
import OAI.NumberTheory.Ostmann.Conclusion.SelectedCovarianceComplex

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open Construction Arithmetic HistoryBulkActualTotalReplacement
open HistoryBulkFibreGiantErrorAverage
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem selectedCovariance_le_norm_relative_plainOriginal
    (C : InitialSourceChoice d Bs BD Bz k L E) (spectator : PrimeSource)
    (a b : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2)))) :
    selectedCovariance C spectator (bulkSize k L/2) l a b ≤
      ‖plainOriginalAverage C spectator (a⁻¹*b) false‖ := by
  apply selectedCovariance_le_of_complex_norm
  rw [selectedComplexCovariance_eq_originalSourceAverage]
  exact le_rfl

end Ostmann.Conclusion

end

end OAI
