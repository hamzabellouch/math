import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregationBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction CompensationEqualityPatterns HistoryPairSourceLaws
open HistoryBulkUniversalPatternAggregation

theorem patternComplexSum_congr_pointwise {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sources : SourceFamily) (origin τ : ι → ℕ)
    (F G : ∀p : Pattern τ,(Block p → CommonSample sources origin) → ℂ)
    (h : ∀p b,F p b=G p b) :
    patternComplexSum sources origin τ F=patternComplexSum sources origin τ G :=
  congrArg (patternComplexSum sources origin τ) (funext fun p=>funext (h p))

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
