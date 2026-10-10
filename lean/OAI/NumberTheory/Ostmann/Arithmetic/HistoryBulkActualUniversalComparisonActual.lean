import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainActual
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalComparisonAssembly
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalComparisonPrincipal
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalComparisonStatement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalComparison
open Construction Conclusion Filter HistoryBulkActualTotalReplacement

theorem actual_universal_comparisons_eventually (d : Decomposition) (BD Bz : ℝ)
    (hBD : 0≤BD) (hBz : 9≤Bz) (k : ℕ) (hk : 2≤k) :
    ActualUniversalEstimates d BD Bz k :=
  universal_comparisons_of_estimates d BD Bz k hk
    (actual_plainFinal_eventually d BD Bz hBD hBz k hk)
    (selected_plain_total_error_eventually d 200 BD Bz 0 (by norm_num) (by norm_num) hk)

end Ostmann.Arithmetic.HistoryBulkActualUniversalComparison

end

end OAI
