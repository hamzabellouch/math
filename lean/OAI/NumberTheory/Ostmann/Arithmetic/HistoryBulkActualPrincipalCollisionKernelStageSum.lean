import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindexPatterns
import OAI.NumberTheory.Ostmann.Construction.OffDiagonalExpectations

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision
open Construction CompensationEqualityPatterns HistoryPairSourceLaws
open HistoryBulkUniversalPatternAggregation HistoryBulkPrincipalSourceReindex
variable {ι κ α β : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [Fintype α] [Fintype β]

private theorem kernelStage_pattern_mul (sources : SourceFamily) (origin τ : ι → ℕ)
    (c : ℂ) (F : ∀p : Pattern τ,(Block p → CommonSample sources origin) → ℂ) :
    patternComplexSum sources origin τ (fun p b => c * F p b) =
      c * patternComplexSum sources origin τ F := by
  classical
  unfold patternComplexSum
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> ring

private theorem kernelStage_pattern_cmean (sources : SourceFamily) (origin τ : ι → ℕ)
    (μ : FinitePrior α)
    (F : α → ∀p : Pattern τ,(Block p → CommonSample sources origin) → ℂ) :
    patternComplexSum sources origin τ (fun p b => μ.cmean (fun u => F u p b)) =
      μ.cmean (fun u => patternComplexSum sources origin τ (F u)) := by
  unfold FinitePrior.cmean
  rw [patternComplexSum_sum]
  apply Finset.sum_congr rfl
  intro u _
  exact kernelStage_pattern_mul sources origin τ (μ.mass u : ℂ) (F u)

theorem kernelStage_sum_cmean_pattern (sources : SourceFamily) (origin τ : ι → ℕ)
    (ν : FinitePrior β) (μ : FinitePrior α)
    (F : κ → β → α → ∀p : Pattern τ,(Block p → CommonSample sources origin) → ℂ) :
    (∑ i : κ, ν.cmean (fun bg => μ.cmean (fun u =>
      patternComplexSum sources origin τ (F i bg u)))) =
    ν.cmean (fun bg => patternComplexSum sources origin τ
      (fun p b => ∑ i : κ, μ.cmean (fun u => F i bg u p b))) := by
  rw [←FinitePrior.cmean_sum]
  apply congrArg ν.cmean
  funext bg
  rw [←FinitePrior.cmean_sum]
  rw [patternComplexSum_sum, FinitePrior.cmean_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (kernelStage_pattern_cmean sources origin τ μ (F i bg)).symm

theorem kernelStage_option_cmean_mul {δ : Type*} (μ : FinitePrior α)
    (o : Option δ) (K : δ → ℂ) (F : δ → α → ℂ) :
    μ.cmean (fun u => o.elim 0 (fun r => K r * F r u)) =
      o.elim 0 (fun r => K r * μ.cmean (F r)) := by
  cases o with
  | none => simp only [Option.elim_none, FinitePrior.cmean, mul_zero, Finset.sum_const_zero]
  | some r => exact FinitePrior.cmean_mul_left μ (K r) (F r)

end Ostmann.Arithmetic.HistoryBulkActualPrincipalCollision

end

end OAI
