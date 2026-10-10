import OAI.NumberTheory.Ostmann.Arithmetic.CompensationEqualityPatternsLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationBiasedKernelSum

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelectedSum
open Construction CompensationEqualityPatterns HistoryPairSourceLaws
open HistoryCompensationBiasedKernelSum
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem original_error_sum_norm_le_biasedKernelSum
    (sources : SourceFamily) (origin τ : ι → ℕ)
    (K : ∀ p : Pattern τ, (Block p → CommonSample sources origin) → Block p → ℝ)
    (mask : ∀ p : Pattern τ, (Block p → CommonSample sources origin) → ℝ)
    (δ : ℝ) (e : ∀ p : Pattern τ, BlockDraw p (CommonSample sources origin) → ℂ)
    (_hδ : 0 ≤ δ) (_hK : ∀ p b q, 0 ≤ K p b q)
    (hm : ∀ p b, 0 ≤ mask p b)
    (he : ∀ p b, ‖e p b‖ ≤ δ * ∏ q, K p b.val q) :
    ‖∑ p : Pattern τ, ∑ b : BlockDraw p (CommonSample sources origin),
      (((∏ q, blockWeight p (sourceWeight sources origin) q (b.val q)) *
        (∏ i : ι, ((expand p b i).val : ℝ)) : ℝ) : ℂ) *
          ((mask p b.val : ℂ) * e p b)‖ ≤
      δ * biasedKernelSum sources origin τ K mask := by
  let W : ∀ p : Pattern τ, BlockDraw p (CommonSample sources origin) → ℝ :=
    fun p b => (∏ q, blockWeight p (sourceWeight sources origin) q (b.val q)) *
      (∏ i : ι, ((expand p b i).val : ℝ))
  have hW : ∀ p b, 0 ≤ W p b := by
    intro p b
    exact mul_nonneg (source_block_mass_nonneg sources origin τ p b)
      (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _))
  change ‖∑ p : Pattern τ, ∑ b : BlockDraw p (CommonSample sources origin),
    (W p b : ℂ) * ((mask p b.val : ℂ) * e p b)‖ ≤ _
  calc
    _ ≤ ∑ p : Pattern τ, ∑ b : BlockDraw p (CommonSample sources origin),
        ‖(W p b : ℂ) * ((mask p b.val : ℂ) * e p b)‖ := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun p _ => norm_sum_le _ _)
    _ ≤ ∑ p : Pattern τ, ∑ b : BlockDraw p (CommonSample sources origin),
        δ * (W p b * (mask p b.val * ∏ q, K p b.val q)) := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro b _
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hW p b),
        abs_of_nonneg (hm p b.val)]
      calc
        _ ≤ W p b * (mask p b.val * (δ * ∏ q, K p b.val q)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (he p b) (hm p b.val)) (hW p b)
        _ = _ := by ring
    _ = δ * (∑ p : Pattern τ, ∑ b : BlockDraw p (CommonSample sources origin),
        W p b * (mask p b.val * ∏ q, K p b.val q)) := by
      simp only [Finset.mul_sum]
    _ = δ * biasedKernelSum sources origin τ K mask :=
      congrArg (fun t : ℝ => δ * t) (original_sum_eq_biasedKernelSum sources origin τ K mask)

end Ostmann.Arithmetic.HistoryPairVariableBSquareErrorSelectedSum

end

end OAI
