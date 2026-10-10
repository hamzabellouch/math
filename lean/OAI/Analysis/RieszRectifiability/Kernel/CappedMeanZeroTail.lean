import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.CappedTransform
import OAI.Analysis.RieszRectifiability.Kernel.FarRieszTransform

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Filter Set

theorem scalarCappedRieszKernel_far_center_difference {d : ℕ} (m : ℕ)
    (e a x y : Ambient d) (H ε : ℝ) (hH : 0 < H) (hεH : ε ≤ H)
    (hy : dist y a ≤ H) (hx : 2 * H ≤ dist a x) :
    |scalarCappedRieszKernel m e ε (x, y) - scalarCappedRieszKernel m e ε (x, a)| ≤
      ((2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) * (‖e‖ * H)) *
        inverseDistancePow (m + 1) a x := by
  have hxy : ε ≤ dist x y := by
    have ht := dist_triangle a y x
    rw [dist_comm a y, dist_comm y x] at ht
    linarith
  have hxa : ε ≤ dist x a := by rw [dist_comm x a]; linarith
  have heq : scalarCappedRieszKernel m e ε (x, y) - scalarCappedRieszKernel m e ε (x, a) =
      -inner ℝ e (kernel m y x - kernel m a x) := by
    rw [scalarCappedRieszKernel, scalarCappedRieszKernel,
      cappedRieszKernel_eq_kernel m ε (x, y) hxy,
      cappedRieszKernel_eq_kernel m ε (x, a) hxa,
      kernel_antisymm m y x, kernel_antisymm m a x]
    simp only [inner_neg_right, inner_sub_right]
    ring
  rw [heq, abs_neg]
  apply (scalar_far_kernel_bound m e a y x (2 * H) (by linarith) (by linarith) hx).trans
  apply mul_le_mul_of_nonneg_right _ (inverseDistancePow_nonneg _ _ _)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hy (norm_nonneg _)) (by positivity)

theorem scalarCappedTransform_mean_zero_tail {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (e a : Ambient d) (H ε : ℝ)
    (hH : 0 < H) (hε : 0 < ε) (hεH : ε ≤ H)
    (g : Ambient d → ℝ) (hgm : Measurable g) (hg : Integrable g μ)
    (hmean : (∫ y, g y ∂μ) = 0) (hgs : ∀ y, g y ≠ 0 → dist y a ≤ H)
    (x : Ambient d) (hx : 2 * H ≤ dist a x) :
    |scalarCappedTransform m μ e ε g x| ≤
      ((∫ y, |g y| ∂μ) *
        ((2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) * (‖e‖ * H))) *
          inverseDistancePow (m + 1) a x := by
  let c := scalarCappedRieszKernel m e ε (x, a)
  let F : Ambient d → ℝ := fun y => g y * (scalarCappedRieszKernel m e ε (x, y) - c)
  let B := ((2 ^ (m + 1) + (m + 1 : ℝ) * 2 ^ (m + 2)) * (‖e‖ * H)) *
    inverseDistancePow (m + 1) a x
  have hcap := (scalarCappedTransform_integrable_and_bound m μ e ε hε g hgm hg x).1
  have hF : Integrable F μ := by
    have heq : F = fun y => g y * scalarCappedRieszKernel m e ε (x, y) - g y * c := by
      funext y
      dsimp only [F]
      ring
    rw [heq]
    exact hcap.sub (hg.mul_const c)
  have hId : (∫ y, F y ∂μ) = scalarCappedTransform m μ e ε g x := by
    simp only [F, mul_sub]
    rw [integral_sub hcap (hg.mul_const c), integral_mul_const, hmean, zero_mul, sub_zero]
    rfl
  have hb (y : Ambient d) : |F y| ≤ |g y| * B := by
    by_cases hy : g y = 0
    · simp only [F, hy, zero_mul, abs_zero, le_refl]
    · dsimp only [F, B, c]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (scalarCappedRieszKernel_far_center_difference m e a x y H ε hH hεH (hgs y hy) hx)
        (abs_nonneg _)
  rw [← hId]
  calc
    _ ≤ ∫ y, |F y| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ y, |g y| * B ∂μ := integral_mono hF.abs (hg.abs.mul_const B) hb
    _ = _ := by rw [integral_mul_const]; dsimp only [B]; ring

end

end RieszRectifiability

end OAI
