import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRegularComplexEnergy
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! Vanishing small-ball gradient energy for complex radial channels. -/

open Set MeasureTheory
open scoped ContDiff
namespace DefocusingNLS

theorem homogeneousRegular_gradient_zero (R : ℝ) (hR : 0 < R)
    (F : ℝ → ℂ) (hF : ContDiff ℝ 1 F) (hFR : F R = 0)
    (hE : (∫ r in (0 : ℝ)..R, r ^ 11 * ‖deriv F r‖ ^ 2) = 0) :
    ∀ r ∈ Icc 0 R, F r = 0 := by
  let G := fun r => r ^ 11 * ‖deriv F r‖ ^ 2
  have hGc : Continuous G := by
    dsimp only [G]
    exact (continuous_id.pow 11).mul (hF.continuous_deriv_one.norm.pow 2)
  have hGn : ∀ r ∈ Icc 0 R, 0 ≤ G r := by
    intro r hr
    exact mul_nonneg (pow_nonneg hr.1 11) (sq_nonneg _)
  have hdf : EqOn (deriv F) (fun _ => 0) (Ioo 0 R) := by
    intro r hr
    by_contra hn
    have hGp : 0 < G r :=
      mul_pos (pow_pos hr.1 11) (sq_pos_of_pos (norm_pos_iff.mpr hn))
    have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      hR (show ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 R) from continuousOn_const)
      hGc.continuousOn (fun x hx => hGn x ⟨hx.1.le, hx.2⟩)
      ⟨r, ⟨hr.1.le, hr.2.le⟩, hGp⟩
    simp only [intervalIntegral.integral_zero] at hi
    exact (ne_of_gt hi) hE
  have hclosed : EqOn (deriv F) (fun _ => 0) (Icc 0 R) := by
    have he := hdf.closure hF.continuous_deriv_one continuous_const
    rwa [closure_Ioo hR.ne] at he
  intro r hr
  have he := Convex.norm_image_sub_le_of_norm_deriv_le (C := 0)
    (fun x (_ : x ∈ Icc 0 R) => hF.differentiable (by norm_num) x)
    (fun x hx => by rw [hclosed hx]; simp) (convex_Icc 0 R) hr (right_mem_Icc.mpr hR.le)
  simpa only [hFR, zero_sub, norm_neg, zero_mul, norm_le_zero_iff] using he

end DefocusingNLS

end OAI
