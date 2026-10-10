import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalComparisonActual
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalComparisonProviderAssembly
import OAI.NumberTheory.Ostmann.Conclusion.ActualComparisonProviders

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalComparison
open Construction Conclusion Filter

theorem actual_singleComparisonProvider (d : Decomposition) :
    ActualSingleComparisonProvider d 17 :=
  single_provider_of_universal_estimates d (actual_universal_comparisons_eventually d)

theorem actual_badCovarianceComparisonProvider (d : Decomposition) :
    ActualBadCovarianceComparisonProvider d 17 :=
  bad_provider_of_universal_estimates d (actual_universal_comparisons_eventually d)

end Ostmann.Arithmetic.HistoryBulkActualUniversalComparison

end

end OAI
