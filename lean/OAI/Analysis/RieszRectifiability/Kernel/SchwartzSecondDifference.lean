import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set
open scoped NNReal

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def symmetricSecondDifference (g : Ambient d → F) (x h : Ambient d) : F :=
  g (x + h) + g (x - h) - (2 : ℝ) • g x

theorem first_order_remainder_of_lipschitz_derivative (g : Ambient d → F)
    (hg : Differentiable ℝ g) (L : ℝ≥0) (hL : LipschitzWith L (fderiv ℝ g))
    (x h : Ambient d) :
    ‖g (x + h) - g x - fderiv ℝ g x h‖ ≤ (L : ℝ) * ‖h‖ ^ 2 := by
  have hbound : ∀ y ∈ segment ℝ x (x + h),
      ‖fderiv ℝ g y - fderiv ℝ g x‖ ≤ (L : ℝ) * ‖h‖ := by
    intro y hy
    calc
      _ ≤ (L : ℝ) * ‖y - x‖ := hL.norm_sub_le y x
      _ ≤ (L : ℝ) * ‖h‖ := by
        apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
        simpa only [add_sub_cancel_left] using! norm_sub_le_of_mem_segment hy
  have hh := (convex_segment x (x + h)).norm_image_sub_le_of_norm_fderiv_le'
    (fun y _ => hg y) hbound (left_mem_segment ℝ x (x + h)) (right_mem_segment ℝ x (x + h))
  simpa only [add_sub_cancel_left, pow_two, mul_assoc] using! hh

theorem second_difference_of_lipschitz_derivative (g : Ambient d → F)
    (hg : Differentiable ℝ g) (L : ℝ≥0) (hL : LipschitzWith L (fderiv ℝ g))
    (x h : Ambient d) :
    ‖symmetricSecondDifference g x h‖ ≤ 2 * (L : ℝ) * ‖h‖ ^ 2 := by
  have hp := first_order_remainder_of_lipschitz_derivative g hg L hL x h
  have hm := first_order_remainder_of_lipschitz_derivative g hg L hL x (-h)
  have heq : symmetricSecondDifference g x h =
      (g (x + h) - g x - fderiv ℝ g x h) +
      (g (x + -h) - g x - fderiv ℝ g x (-h)) := by
    simp only [symmetricSecondDifference, map_neg, sub_eq_add_neg, two_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖g (x + h) - g x - fderiv ℝ g x h‖ +
        ‖g (x + -h) - g x - fderiv ℝ g x (-h)‖ := norm_add_le _ _
    _ ≤ (L : ℝ) * ‖h‖ ^ 2 + (L : ℝ) * ‖-h‖ ^ 2 := add_le_add hp hm
    _ = _ := by rw [norm_neg]; ring

theorem schwartz_second_difference_quadratic_bound (g : 𝓢(Ambient d, F)) (x h : Ambient d) :
    ‖symmetricSecondDifference g x h‖ ≤
      2 * SchwartzMap.seminorm ℝ 0 0
        (fderivCLM ℝ (Ambient d) (Ambient d →L[ℝ] F) (fderivCLM ℝ (Ambient d) F g)) * ‖h‖ ^ 2 := by
  let Dg := fderivCLM ℝ (Ambient d) F g
  let DDg := fderivCLM ℝ (Ambient d) (Ambient d →L[ℝ] F) Dg
  let L : ℝ≥0 := ⟨SchwartzMap.seminorm ℝ 0 0 DDg, apply_nonneg _ _⟩
  have hL : LipschitzWith L Dg := by
    apply lipschitzWith_of_nnnorm_fderiv_le Dg.differentiable
    intro y
    have hb : ‖fderiv ℝ Dg y‖ ≤ (L : ℝ) := DDg.norm_le_seminorm ℝ y
    exact_mod_cast hb
  exact second_difference_of_lipschitz_derivative g g.differentiable L hL x h

theorem schwartz_second_difference_uniform_bound (g : 𝓢(Ambient d, F)) (x h : Ambient d) :
    ‖symmetricSecondDifference g x h‖ ≤ 4 * SchwartzMap.seminorm ℝ 0 0 g := by
  have hp := g.norm_le_seminorm ℝ (x + h)
  have hm := g.norm_le_seminorm ℝ (x - h)
  have hx := g.norm_le_seminorm ℝ x
  calc
    _ ≤ ‖g (x + h) + g (x - h)‖ + ‖(2 : ℝ) • g x‖ := norm_sub_le _ _
    _ ≤ (‖g (x + h)‖ + ‖g (x - h)‖) + ‖(2 : ℝ) • g x‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ _ := by rw [norm_smul]; norm_num; linarith

end

end RieszRectifiability

end OAI
