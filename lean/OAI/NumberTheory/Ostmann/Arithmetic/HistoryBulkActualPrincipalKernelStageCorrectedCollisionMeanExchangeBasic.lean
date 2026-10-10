import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexExchange

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected
open Construction CompensationEqualityPatterns HistoryPairSourceLaws
open HistoryBulkUniversalPatternAggregation HistoryBulkActualPrincipalSourceReindex

theorem sum_pattern_cmean_exchange {ι α β κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β] [Fintype κ]
    (sources : SourceFamily) (origin τ : ι → ℕ) (μ : FinitePrior α) (ν : FinitePrior β)
    (F : κ → β → α → ∀p : Pattern τ,(Block p → CommonSample sources origin) → ℂ) :
    (∑i,ν.cmean (fun bg=>μ.cmean (fun u=>patternComplexSum sources origin τ (F i bg u)))) =
      ν.cmean (fun bg=>patternComplexSum sources origin τ
        (fun p b=>∑i,μ.cmean (fun u=>F i bg u p b))) := by
  rw [←FinitePrior.cmean_sum]
  apply congrArg ν.cmean
  funext bg
  rw [←FinitePrior.cmean_sum,←pattern_root_cmean_exchange]

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStageCorrected

end

end OAI
