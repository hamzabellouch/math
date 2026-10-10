import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregationOriginalBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregation
open Construction CompensationEqualityPatterns HistoryPairSourceLaws
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem original_occurrence_sum_eq_patternComplexSum (sources : SourceFamily)
    (origin τ : ι → ℕ) (F : (ι → CommonSample sources origin) → ℂ) :
    (∑ w : ι → CommonSample sources origin,
      (((∏ i, sourceWeight sources origin i (w i)) *
        (∏ i, ((w i).val : ℝ)) : ℝ) : ℂ)*F w) =
      patternComplexSum sources origin τ (fun p b => F (fun i => b (label p i))) := by
  rw [sum_eq_patterns τ]
  simp_rw [product_weights_by_blocks]
  exact sum_pattern_original_eq_patternComplexSum sources origin τ
    (fun p b => F (fun i => b (label p i)))

theorem original_source_cmean_eq_patternComplexSum (sources : SourceFamily)
    (origin τ : ι → ℕ) (F : (ι → CommonSample sources origin) → ℂ) :
    (dependentProductPrior (fun i => (sources (origin i)).law)).cmean
      (fun x => (((∏ i, ((x i).val : ℝ)) : ℝ) : ℂ)*F (tupleEmbed sources origin x)) =
      patternComplexSum sources origin τ (fun p b => F (fun i => b (label p i))) := by
  have h := source_cmean_eq_patterns sources origin τ
    (fun w => (((∏ i, ((w i).val : ℝ)) : ℝ) : ℂ)*F w)
  have hF (p : Pattern τ) (b : BlockDraw p (CommonSample sources origin)) :
      F (expand p b)=F (fun i => b.val (label p i)) := rfl
  simp_rw [hF] at h
  rw [← sum_pattern_original_eq_patternComplexSum sources origin τ
    (fun p b => F (fun i => b (label p i)))]
  simpa only [tupleEmbed, sourceEmbed, Complex.real_smul, Complex.ofReal_mul,
    mul_assoc, expand] using h

end Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregation

end

end OAI
