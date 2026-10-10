import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeGaussTailRange
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstTailHeightPrefix
import OAI.NumberTheory.CubicMoment.Estimates.PrimeTailHeckeTail

namespace OAI

/-! A single actual product window is a difference of aligned full tails. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma envelopeCutoffBilinearTail_window_sum (P S : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (W : ℝ → ℂ) (H T X : ℝ) :
    envelopeCutoffBilinearTail P S α β W H T X =
      ∑ j ∈ Finset.range (heightWindowCount H T),
        productGaussWindow P S α β 0 W H (T*(3/2:ℝ)^j) X := by
  unfold envelopeCutoffBilinearTail productGaussWindow
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [productGaussHeightWindowKernel,theta_zero,one_mul]
  ring

lemma productGaussWindow_eq_tail_sub (P S : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (W : ℝ → ℂ) {H T : ℝ}
    (hH : 0 < H) (hT : 0 < T) (hcap : T < 2*Real.pi*H) (X : ℝ) :
    productGaussWindow P S α β 0 W H T X =
      envelopeCutoffBilinearTail P S α β W H T X-
        envelopeCutoffBilinearTail P S α β W H (T*(3/2)) X := by
  have hc : 1 ≤ heightWindowCount H T := by
    by_contra hn
    have hz : heightWindowCount H T = 0 := by omega
    have hb := heightWindowCount_covers hH hT
    rw [hz,pow_zero,mul_one] at hb
    exact (not_le_of_gt hcap) hb
  rw [envelopeCutoffBilinearTail_window_sum,envelopeCutoffBilinearTail_window_sum]
  simpa only [Finset.sum_range_one,pow_zero,mul_one,pow_one] using
    geometricHeight_prefix (fun U => productGaussWindow P S α β 0 W H U X) hH hT hc

end CubicFirstMoment

end

end OAI
