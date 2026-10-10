import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.RenormalizedFarPairing

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def vectorKernelFarConstant (n : ℕ) : ℝ :=
  (n + 1 : ℝ) * 2 ^ (n + 2) + 2 ^ (n + 1)

theorem vectorKernelFarConstant_pos (n : ℕ) : 0 < vectorKernelFarConstant n := by
  unfold vectorKernelFarConstant
  positivity

theorem vector_kernel_difference_identity {d : ℕ} (n : ℕ) (a x y : Ambient d) :
    kernel n x y - kernel n a y =
      (inverseDistancePow (n + 1) x y - inverseDistancePow (n + 1) a y) • (a - y) +
        inverseDistancePow (n + 1) x y • (x - a) := by
  simp only [kernel, inverseDistancePow, dist_eq_norm]
  module

theorem vector_kernel_far_difference {d : ℕ} (n : ℕ) (a x y : Ambient d)
    (hy : 0 < dist a y) (hfar : 2 * dist x a ≤ dist a y) :
    ‖kernel n x y - kernel n a y‖ ≤
      vectorKernelFarConstant n * dist x a * inverseDistancePow (n + 1) a y := by
  have hd := inverseDistancePow_far_difference n a x y hy hfar
  have hi := inverseDistancePow_far_le (n + 1) a x y hy hfar
  rw [vector_kernel_difference_identity]
  calc
    _ ≤ ‖(inverseDistancePow (n + 1) x y - inverseDistancePow (n + 1) a y) • (a - y)‖ +
        ‖inverseDistancePow (n + 1) x y • (x - a)‖ := norm_add_le _ _
    _ = |inverseDistancePow (n + 1) x y - inverseDistancePow (n + 1) a y| * dist a y +
        inverseDistancePow (n + 1) x y * dist x a := by
      simp only [norm_smul, Real.norm_eq_abs, ← dist_eq_norm,
        abs_of_nonneg (inverseDistancePow_nonneg _ _ _), Real.dist_eq]
    _ ≤ ((n + 1 : ℝ) * 2 ^ (n + 2) * dist x a * inverseDistancePow (n + 2) a y) * dist a y +
        (2 ^ (n + 1) * inverseDistancePow (n + 1) a y) * dist x a :=
      add_le_add (mul_le_mul_of_nonneg_right hd (dist_nonneg))
        (mul_le_mul_of_nonneg_right hi (dist_nonneg))
    _ = _ := by
      unfold vectorKernelFarConstant inverseDistancePow
      rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
      field_simp; ring

end

end RieszRectifiability

end OAI
