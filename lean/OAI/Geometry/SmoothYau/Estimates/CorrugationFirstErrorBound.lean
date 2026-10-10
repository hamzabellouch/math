import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.PulledGradient

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem corrugation_first_error_bound {ψ χ : E → ℝ} {F : V → ℝ} {y : E → V}
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hF : ContDiff ℝ ∞ F) (hy : ContDiff ℝ ∞ y) (c N : ℝ) (x v : E) :
    |fderiv ℝ (fun z => ψ z+c*χ z*F (N • y z)) x v -
      (fderiv ℝ ψ x v+c*χ x*N*fderiv ℝ F (N • y x) (fderiv ℝ y x v))| ≤
      |c| *‖fderiv ℝ χ x‖*|F (N • y x)| *‖v‖ := by
  rw [corrugation_first hψ hχ hF hy]
  have heq : fderiv ℝ ψ x v + c*fderiv ℝ χ x v*F (N • y x) +
      c*χ x*N*fderiv ℝ F (N • y x) (fderiv ℝ y x v) -
      (fderiv ℝ ψ x v+c*χ x*N*fderiv ℝ F (N • y x) (fderiv ℝ y x v)) =
      c*fderiv ℝ χ x v*F (N • y x) := by ring
  rw [heq,abs_mul,abs_mul]
  have hb : |fderiv ℝ χ x v| ≤ ‖fderiv ℝ χ x‖*‖v‖ := by
    simpa only [Real.norm_eq_abs] using (fderiv ℝ χ x).le_opNorm v
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb (abs_nonneg c)) (abs_nonneg (F (N • y x)))
  nlinarith only [hh]
end YauCounterexamples

end

end OAI
