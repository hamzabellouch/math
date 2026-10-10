import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementPlainActual
import OAI.NumberTheory.Ostmann.Conclusion.ActualComparisonProviders
import OAI.NumberTheory.Ostmann.Conclusion.ActualGoodCovarianceComparisonAssembly

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Conclusion
open Arithmetic HistoryBulkActualTotalReplacement

theorem actualGoodCovarianceComparisonProvider (d : Decomposition) :
    ActualGoodCovarianceComparisonProvider d :=
  actualGoodCovarianceComparisonProvider_of_total d (fun BD Bz k hk =>
    selected_plain_total_error_eventually d 200 BD Bz (67*(2:ℝ)^k)
      (Nat.cast_nonneg 200)
      (mul_nonneg (Nat.cast_nonneg 67) (pow_nonneg (Nat.cast_nonneg 2) k)) hk)

end Ostmann.Conclusion

end

end OAI
