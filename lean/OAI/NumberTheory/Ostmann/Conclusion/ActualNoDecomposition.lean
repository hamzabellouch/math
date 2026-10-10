import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalComparison
import OAI.NumberTheory.Ostmann.Conclusion.ActualDiagonalGoodComparison
import OAI.NumberTheory.Ostmann.Conclusion.ActualFourComparisonConsumer
import OAI.NumberTheory.Ostmann.Conclusion.ActualGoodCovarianceComparison
import OAI.NumberTheory.Ostmann.Setup

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Conclusion

theorem actual_no_decomposition : ∀ _d : Decomposition, False :=
  no_decomposition_of_actual_four_comparison_providers 17 17
    Ostmann.Arithmetic.HistoryBulkActualUniversalComparison.actual_singleComparisonProvider
    actual_diagonal_good_comparison_provider
    Ostmann.Arithmetic.HistoryBulkActualUniversalComparison.actual_badCovarianceComparisonProvider
    actualGoodCovarianceComparisonProvider

end Ostmann.Conclusion

end OAI
