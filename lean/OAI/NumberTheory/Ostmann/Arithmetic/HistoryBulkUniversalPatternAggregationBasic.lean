import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationBiasedKernelSumSelected

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregation
open Construction CompensationEqualityPatterns HistoryPairSourceLaws HistoryCompensationPatternBudget
open HistoryCompensationBiasedKernelSum
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def patternWeight (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ}
    (p : Pattern τ) (b : Block p → CommonSample sources origin) : ℝ :=
  (∏q,biasedBlockWeight sources origin p q (b q))*(∏q,((b q).val:ℝ))

omit [DecidableEq ι] in
theorem patternWeight_nonneg (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ}
    (p : Pattern τ) (b : Block p → CommonSample sources origin) :
    0 ≤ patternWeight sources origin p b :=
  mul_nonneg (Finset.prod_nonneg (fun q _=>biasedBlockWeight_nonneg sources origin p q (b q)))
    (Finset.prod_nonneg (fun _q _=>Nat.cast_nonneg _))

def patternComplexSum (sources : SourceFamily) (origin τ : ι → ℕ)
    (F : ∀p : Pattern τ,(Block p → CommonSample sources origin) → ℂ) : ℂ :=
  ∑p : Pattern τ,∑b : Block p → CommonSample sources origin,
    (patternWeight sources origin p b:ℂ)*
      (if Function.Injective (fun q=>(blockType p q,b q)) then F p b else 0)

theorem norm_patternComplexSum_le_kernelSum (sources : SourceFamily) (origin τ : ι → ℕ)
    (F : ∀p : Pattern τ,(Block p → CommonSample sources origin) → ℂ)
    (A : ℝ) (hF : ∀p b,patternWeight sources origin p b≠0  → 
      Function.Injective (fun q=>(blockType p q,b q))  → 
      ‖F p b‖ ≤ A*∏q : Block p,2/((b q).val:ℝ)) :
    ‖patternComplexSum sources origin τ F‖ ≤
      A*biasedKernelSum sources origin τ (fun _ b q=>2/((b q).val:ℝ)) (fun _ _=>1) := by
  unfold patternComplexSum biasedKernelSum
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro p hp
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro b hb
  by_cases hw : patternWeight sources origin p b=0
  · simp only [hw,Complex.ofReal_zero,zero_mul,norm_zero]
    change 0 ≤ A*(patternWeight sources origin p b*_)
    rw [hw,zero_mul,mul_zero]
  by_cases hd : Function.Injective (fun q=>(blockType p q,b q))
  · simp only [ite_true,hd,one_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (patternWeight_nonneg sources origin p b)]
    have hh := mul_le_mul_of_nonneg_left (hF p b hw hd) (patternWeight_nonneg sources origin p b)
    simpa only [patternWeight,mul_left_comm] using hh
  · simp only [hd,ite_false,mul_zero,norm_zero,le_refl]

end Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregation

end

end OAI
