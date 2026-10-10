import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementCorrectedActual
import OAI.NumberTheory.Ostmann.Conclusion.ActualComparisonProviders
import OAI.NumberTheory.Ostmann.Conclusion.ActualDiagonalGoodComparisonAssembly

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open Construction Arithmetic
open HistoryBulkActualTotalReplacement

theorem actual_diagonal_good_comparison_provider (d : Decomposition) :
    ActualDiagonalGoodComparisonProvider d :=
  actual_diagonal_good_comparison_of_residual d
    (fun BD Bz H {_k} hH hk =>
      selected_corrected_total_error_eventually d 200 BD Bz H
        (Nat.cast_nonneg 200) hH hk)

end Ostmann.Conclusion

end

end OAI
