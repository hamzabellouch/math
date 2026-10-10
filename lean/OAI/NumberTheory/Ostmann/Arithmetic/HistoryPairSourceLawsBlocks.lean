import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationPatternBudgetBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsCarriers

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairSourceLaws
open Construction CompensationEqualityPatterns
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def biasedBlockWeight (sources : SourceFamily) (origin : ι → ℕ)
    {τ : ι → ℕ} (p : Pattern τ) (q : Block p) (v : CommonSample sources origin) : ℝ :=
  blockWeight p (sourceWeight sources origin) q v * (v.val : ℝ)^multiplicity p q / (v.val : ℝ)

def blockAnchor {τ : ι → ℕ} (p : Pattern τ) (q : Block p) : Fiber p q :=
  Classical.choice (fiber_nonempty p q)

omit [DecidableEq ι] in

theorem biasedBlockWeight_mul_prime (sources : SourceFamily) (origin : ι → ℕ)
    {τ : ι → ℕ} (p : Pattern τ) (q : Block p) (v : CommonSample sources origin) :
    biasedBlockWeight sources origin p q v * (v.val : ℝ) =
      blockWeight p (sourceWeight sources origin) q v * (v.val : ℝ)^multiplicity p q := by
  have hv : (v.val : ℝ) ≠ 0 := by exact_mod_cast (commonSample_prime sources origin v).ne_zero
  exact div_mul_cancel₀ _ hv

omit [DecidableEq ι] in

theorem biased_product_jacobian (sources : SourceFamily) (origin : ι → ℕ)
    {τ : ι → ℕ} (p : Pattern τ) (b : BlockDraw p (CommonSample sources origin)) :
    (∏ q, biasedBlockWeight sources origin p q (b.val q)) *
        (∏ q, ((b.val q).val : ℝ)) =
      (∏ q, blockWeight p (sourceWeight sources origin) q (b.val q)) *
        (∏ i, ((expand p b i).val : ℝ)) := by
  rw [product_by_multiplicity p b (fun v => (v.val : ℝ)), ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun q _ => biasedBlockWeight_mul_prime sources origin p q (b.val q))

omit [DecidableEq ι] in

theorem blockDraw_sum_indicator {τ : ι → ℕ} (p : Pattern τ) {κ : Type*} [Fintype κ]
    (F : BlockDraw p κ → ℝ) :
    (∑ b : BlockDraw p κ, F b) =
      ∑ b : Block p → κ, if h : Function.Injective (fun q => (blockType p q,b q))
        then F ⟨b,h⟩ else 0 := by
  classical
  apply Fintype.sum_of_injective (fun b : BlockDraw p κ => b.val) Subtype.val_injective
  · intro b hb
    have hn : ¬ Function.Injective (fun q => (blockType p q,b q)) :=
      fun h => hb ⟨⟨b,h⟩,rfl⟩
    simp only [hn, dite_false]
  · intro b
    simp only [b.property, dite_true]
    rfl

omit [DecidableEq ι] in

theorem original_block_sum_eq_biased (sources : SourceFamily) (origin : ι → ℕ)
    {τ : ι → ℕ} (p : Pattern τ)
    (F : BlockDraw p (CommonSample sources origin) → ℝ) :
    (∑ b : BlockDraw p (CommonSample sources origin),
      ((∏ q, blockWeight p (sourceWeight sources origin) q (b.val q)) *
        (∏ i, ((expand p b i).val : ℝ)))*F b) =
      ∑ b : Block p → CommonSample sources origin,
        (∏ q, biasedBlockWeight sources origin p q (b q)) *
          (∏ q, ((b q).val : ℝ)) *
          (if h : Function.Injective (fun q => (blockType p q,b q)) then F ⟨b,h⟩ else 0) := by
  simp_rw [← biased_product_jacobian sources origin p]
  rw [blockDraw_sum_indicator]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp

end Ostmann.Arithmetic.HistoryPairSourceLaws

end

end OAI
