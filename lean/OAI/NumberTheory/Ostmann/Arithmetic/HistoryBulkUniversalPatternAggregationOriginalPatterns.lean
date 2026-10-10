import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregationOriginal

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregation
open Construction CompensationEqualityPatterns HistoryPairSourceLaws
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def originalPatternTest (sources : SourceFamily) (origin τ : ι → ℕ)
    (F : ∀ p : Pattern τ,(Block p → CommonSample sources origin) → ℂ)
    (w : ι → CommonSample sources origin) : ℂ :=
  F (patternOf τ w) (collapse (patternOf τ w) ⟨w,rfl⟩).val

omit [DecidableEq ι] in
theorem originalPatternTest_eq [DecidableEq ι] (sources : SourceFamily) (origin τ : ι → ℕ)
    (F : ∀ p : Pattern τ,(Block p → CommonSample sources origin) → ℂ)
    (p : Pattern τ) (w : ι → CommonSample sources origin) (h : patternOf τ w=p) :
    originalPatternTest sources origin τ F w=F p (collapse p ⟨w,h⟩).val := by
  cases h
  rfl

theorem originalPatternTest_expand (sources : SourceFamily) (origin τ : ι → ℕ)
    (F : ∀ p : Pattern τ,(Block p → CommonSample sources origin) → ℂ)
    (p : Pattern τ) (b : BlockDraw p (CommonSample sources origin)) :
    originalPatternTest sources origin τ F (expand p b)=F p b.val := by
  rw [originalPatternTest_eq sources origin τ F p (expand p b) (patternOf_expand p b)]
  exact congrArg (fun z : BlockDraw p (CommonSample sources origin) => F p z.val)
    ((fiberEquiv p).apply_symm_apply b)

theorem original_occurrence_pattern_sum_eq_patternComplexSum (sources : SourceFamily)
    (origin τ : ι → ℕ)
    (F : ∀ p : Pattern τ,(Block p → CommonSample sources origin) → ℂ) :
    (∑ w : ι → CommonSample sources origin,
      (((∏ i, sourceWeight sources origin i (w i)) *
        (∏ i, ((w i).val : ℝ)) : ℝ) : ℂ)*originalPatternTest sources origin τ F w) =
      patternComplexSum sources origin τ F := by
  rw [sum_eq_patterns τ]
  simp_rw [product_weights_by_blocks,originalPatternTest_expand]
  exact sum_pattern_original_eq_patternComplexSum sources origin τ F

theorem original_source_pattern_cmean_eq_patternComplexSum (sources : SourceFamily)
    (origin τ : ι → ℕ)
    (F : ∀ p : Pattern τ,(Block p → CommonSample sources origin) → ℂ) :
    (dependentProductPrior (fun i => (sources (origin i)).law)).cmean
      (fun x => (((∏ i, ((x i).val : ℝ)) : ℝ) : ℂ)*
        originalPatternTest sources origin τ F (tupleEmbed sources origin x)) =
      patternComplexSum sources origin τ F := by
  have h := source_cmean_eq_patterns sources origin τ
    (fun w => (((∏ i, ((w i).val : ℝ)) : ℝ) : ℂ)*originalPatternTest sources origin τ F w)
  rw [← sum_pattern_original_eq_patternComplexSum sources origin τ F]
  simpa only [tupleEmbed,sourceEmbed,Complex.real_smul,Complex.ofReal_mul,mul_assoc,
    originalPatternTest_expand] using h

end Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregation

end

end OAI
