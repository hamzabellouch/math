import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexExchange

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindex
open Construction Conclusion CompensationEqualityPatterns HistoryPairSourceLaws
open HistoryBulkUniversalPatternAggregation
attribute [local instance] Classical.propDecidable

theorem pattern_root_cmean_exchange_of_point
    {ι α β : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]
    (sources : SourceFamily) (origin τ : ι → ℕ) (μ : FinitePrior α)
    (F : β  →  ∀p : Pattern τ,(Block p → CommonSample sources origin) → ℂ)
    (G : β  →  α  →  ∀p : Pattern τ,(Block p → CommonSample sources origin) → ℂ)
    (h : ∀i p b,F i p b=μ.cmean (fun u=>G i u p b)) :
    patternComplexSum sources origin τ (fun p b=>∑i:β,F i p b)=
      μ.cmean (fun u=>∑i:β,patternComplexSum sources origin τ (G i u)) := by
  have he : (fun p b=>∑i:β,F i p b)=
      (fun p b=>∑i:β,μ.cmean (fun u=>G i u p b)) := by
    funext p b
    exact Finset.sum_congr rfl (fun i _=>h i p b)
  exact (congrArg (patternComplexSum sources origin τ) he).trans
    (pattern_root_cmean_exchange sources origin τ μ G)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindex

end

end OAI
