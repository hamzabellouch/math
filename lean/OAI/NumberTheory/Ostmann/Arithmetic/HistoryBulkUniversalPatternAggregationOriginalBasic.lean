import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregationBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregation
open Construction CompensationEqualityPatterns HistoryPairSourceLaws
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem blockDraw_sum_indicator_complex {τ : ι → ℕ} (p : Pattern τ)
    {κ : Type*} [Fintype κ] (F : BlockDraw p κ → ℂ) :
    (∑ b : BlockDraw p κ, F b) =
      ∑ b : Block p → κ, if h : Function.Injective (fun q => (blockType p q,b q))
        then F ⟨b,h⟩ else 0 := by
  apply Fintype.sum_of_injective (fun b : BlockDraw p κ => b.val) Subtype.val_injective
  · intro b hb
    have hn : ¬ Function.Injective (fun q => (blockType p q,b q)) :=
      fun h => hb ⟨⟨b,h⟩,rfl⟩
    simp only [hn, dite_false]
  · intro b
    simp only [b.property, dite_true]
    rfl

omit [DecidableEq ι] in
theorem original_block_sum_eq_biased_complex (sources : SourceFamily) (origin : ι → ℕ)
    {τ : ι → ℕ} (p : Pattern τ)
    (F : BlockDraw p (CommonSample sources origin) → ℂ) :
    (∑ b : BlockDraw p (CommonSample sources origin),
      (((∏ q, blockWeight p (sourceWeight sources origin) q (b.val q)) *
        (∏ i, ((expand p b i).val : ℝ)) : ℝ) : ℂ)*F b) =
      ∑ b : Block p → CommonSample sources origin,
        (patternWeight sources origin p b : ℂ) *
          (if h : Function.Injective (fun q => (blockType p q,b q)) then F ⟨b,h⟩ else 0) := by
  simp_rw [← biased_product_jacobian sources origin p]
  rw [blockDraw_sum_indicator_complex]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp [patternWeight]

theorem sum_pattern_original_eq_patternComplexSum (sources : SourceFamily)
    (origin τ : ι → ℕ)
    (F : ∀ p : Pattern τ,(Block p → CommonSample sources origin) → ℂ) :
    (∑ p : Pattern τ, ∑ b : BlockDraw p (CommonSample sources origin),
      (((∏ q, blockWeight p (sourceWeight sources origin) q (b.val q)) *
        (∏ i, ((expand p b i).val : ℝ)) : ℝ) : ℂ)*F p b.val) =
      patternComplexSum sources origin τ F := by
  unfold patternComplexSum
  apply Finset.sum_congr rfl
  intro p hp
  simpa only [dite_eq_ite] using original_block_sum_eq_biased_complex sources origin p (fun b => F p b.val)

end Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregation

end

end OAI
