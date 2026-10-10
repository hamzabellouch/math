import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexBackground

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindex
open Construction Conclusion CompensationEqualityPatterns HistoryPairSourceLaws
open HistoryBulkUniversalPatternAggregation HistoryBulkPrincipalSourceReindex
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem patternComplexSum_mul_left (sources : SourceFamily) (origin τ : ι → ℕ)
    (c : ℂ) (F : ∀p : Pattern τ,(Block p → CommonSample sources origin) → ℂ) :
    patternComplexSum sources origin τ (fun p b=>c*F p b)=c*patternComplexSum sources origin τ F := by
  classical
  unfold patternComplexSum
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> ring

theorem patternComplexSum_cmean {α : Type*} [Fintype α]
    (sources : SourceFamily) (origin τ : ι → ℕ) (μ : FinitePrior α)
    (F : α → ∀p : Pattern τ,(Block p → CommonSample sources origin) → ℂ) :
    patternComplexSum sources origin τ (fun p b=>μ.cmean (fun u=>F u p b))=
      μ.cmean (fun u=>patternComplexSum sources origin τ (F u)) := by
  unfold FinitePrior.cmean
  rw [patternComplexSum_sum]
  apply Finset.sum_congr rfl
  intro u _
  exact patternComplexSum_mul_left sources origin τ (μ.mass u:ℂ) (F u)

theorem option_cmean {α β : Type*} [Fintype α] (μ : FinitePrior α)
    (r : Option β) (F : β → α → ℂ) :
    r.elim 0 (fun v=>μ.cmean (F v))=μ.cmean (fun u=>r.elim 0 (fun v=>F v u)) := by
  cases r with
  | none => simp only [Option.elim_none,FinitePrior.cmean,mul_zero,Finset.sum_const_zero]
  | some r => rfl

theorem pattern_root_cmean_exchange {α β : Type*} [Fintype α] [Fintype β]
    (sources : SourceFamily) (origin τ : ι → ℕ) (μ : FinitePrior α)
    (F : β → α → ∀p : Pattern τ,(Block p → CommonSample sources origin) → ℂ) :
    patternComplexSum sources origin τ (fun p b=>∑i:β,μ.cmean (fun u=>F i u p b))=
      μ.cmean (fun u=>∑i:β,patternComplexSum sources origin τ (F i u)) := by
  rw [patternComplexSum_sum,FinitePrior.cmean_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact patternComplexSum_cmean sources origin τ μ (F i)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindex

end

end OAI
