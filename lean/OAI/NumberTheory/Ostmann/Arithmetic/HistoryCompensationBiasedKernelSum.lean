import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationBiasedKernelSumBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCompensationBiasedKernelSum
open Construction CompensationEqualityPatterns HistoryPairSourceLaws HistoryCompensationPatternBudget
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def biasedKernelSum (sources : SourceFamily) (origin τ : ι → ℕ)
    (K : ∀p:Pattern τ,(Block p → CommonSample sources origin) → Block p → ℝ)
    (mask : ∀p:Pattern τ,(Block p → CommonSample sources origin) → ℝ) : ℝ :=
  ∑p:Pattern τ,∑b:Block p → CommonSample sources origin,
    (∏q,biasedBlockWeight sources origin p q (b q)) * (∏q,((b q).val:ℝ)) *
      (if Function.Injective (fun q => (blockType p q,b q)) then mask p b*(∏q,K p b q) else 0)

theorem original_sum_eq_biasedKernelSum (sources : SourceFamily) (origin τ : ι → ℕ)
    (K : ∀p:Pattern τ,(Block p → CommonSample sources origin) → Block p → ℝ)
    (mask : ∀p:Pattern τ,(Block p → CommonSample sources origin) → ℝ) :
    (∑p:Pattern τ,∑b:BlockDraw p (CommonSample sources origin),
      ((∏q,blockWeight p (sourceWeight sources origin) q (b.val q))*
        (∏i:ι,((expand p b i).val:ℝ)))*(mask p b.val*∏q,K p b.val q)) =
      biasedKernelSum sources origin τ K mask := by
  unfold biasedKernelSum
  apply Finset.sum_congr rfl
  intro p hp
  exact original_block_sum_eq_biased sources origin p (fun b => mask p b.val*∏q,K p b.val q)

theorem biasedKernelSum_eq_blockDraw (sources : SourceFamily) (origin τ : ι → ℕ)
    (K : ∀p:Pattern τ,(Block p → CommonSample sources origin) → Block p → ℝ)
    (mask : ∀p:Pattern τ,(Block p → CommonSample sources origin) → ℝ) :
    biasedKernelSum sources origin τ K mask =
      ∑p:Pattern τ,∑b:BlockDraw p (CommonSample sources origin),
        (∏q,biasedBlockWeight sources origin p q (b.val q)) * (∏q,((b.val q).val:ℝ)) *
          (mask p b.val*∏q,K p b.val q) := by
  unfold biasedKernelSum
  apply Finset.sum_congr rfl
  intro p hp
  rw [blockDraw_sum_indicator]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp only [mul_zero]

theorem biasedKernelSum_nonneg (sources : SourceFamily) (origin τ : ι → ℕ)
    (K : ∀p:Pattern τ,(Block p → CommonSample sources origin) → Block p → ℝ)
    (mask : ∀p:Pattern τ,(Block p → CommonSample sources origin) → ℝ)
    (hK : ∀p b q,0 ≤ K p b q) (hm : ∀p b,0 ≤ mask p b) :
    0 ≤ biasedKernelSum sources origin τ K mask := by
  rw [biasedKernelSum_eq_blockDraw]
  apply Finset.sum_nonneg
  intro p hp
  apply Finset.sum_nonneg
  intro b hb
  exact mul_nonneg
    (mul_nonneg (Finset.prod_nonneg (fun q _ => biasedBlockWeight_nonneg sources origin p q (b.val q)))
      (Finset.prod_nonneg (fun q _ => Nat.cast_nonneg _)))
    (mul_nonneg (hm p b.val) (Finset.prod_nonneg (fun q _ => hK p b.val q)))

theorem biasedKernelSum_le_caps (sources : SourceFamily) (origin τ : ι → ℕ) (C : ι → ℝ)
    (hcap : ∀i (v:CommonSample sources origin),sourceWeight sources origin i v*(v.val:ℝ) ≤ C i)
    (K : ∀p:Pattern τ,(Block p → CommonSample sources origin) → Block p → ℝ)
    (mask : ∀p:Pattern τ,(Block p → CommonSample sources origin) → ℝ)
    (hK : ∀p b q,0 ≤ K p b q ∧ K p b q ≤ 2/((b q).val:ℝ))
    (hm : ∀p b,0 ≤ mask p b ∧ mask p b ≤ 1) :
    biasedKernelSum sources origin τ K mask  ≤ 
      ∑p:Pattern τ,(2:ℝ)^Fintype.card (Block p)*∏q:Block p,blockCap p C q := by
  rw [biasedKernelSum_eq_blockDraw]
  apply Finset.sum_le_sum
  intro p hp
  apply le_trans _ (pattern_biased_kernel_sum_le sources origin p C hcap (K p) (hK p))
  apply Finset.sum_le_sum
  intro b hb
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (Finset.prod_nonneg (fun q _ => biasedBlockWeight_nonneg sources origin p q (b.val q)))
      (Finset.prod_nonneg (fun q _ => Nat.cast_nonneg _)))
  exact mul_le_of_le_one_left (Finset.prod_nonneg (fun q _ => (hK p b.val q).1)) (hm p b.val).2

end Ostmann.Arithmetic.HistoryCompensationBiasedKernelSum

end

end OAI
