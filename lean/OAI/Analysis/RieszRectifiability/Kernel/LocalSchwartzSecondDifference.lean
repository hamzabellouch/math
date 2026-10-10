import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.SchwartzSecondDifference

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set
open scoped NNReal

variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem first_order_remainder_from_segment_hessian
    (g : Ambient d → F) (hg : Differentiable ℝ g)
    (hdg : Differentiable ℝ (fderiv ℝ g)) (M : ℝ) (hM : 0 ≤ M)
    (x h : Ambient d)
    (hbound : ∀ z ∈ segment ℝ x (x + h), ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ M) :
    ‖g (x + h) - g x - fderiv ℝ g x h‖ ≤ M * ‖h‖ ^ 2 := by
  have hgrad : ∀ z ∈ segment ℝ x (x + h),
      ‖fderiv ℝ g z - fderiv ℝ g x‖ ≤ M * ‖h‖ := by
    intro z hz
    have hh := (convex_segment x (x + h)).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hdg y) hbound (left_mem_segment ℝ x (x + h)) hz
    calc
      _ ≤ M * ‖z - x‖ := hh
      _ ≤ M * ‖h‖ := mul_le_mul_of_nonneg_left
        (by simpa only [add_sub_cancel_left] using! norm_sub_le_of_mem_segment hz) hM
  have hh := (convex_segment x (x + h)).norm_image_sub_le_of_norm_fderiv_le'
    (fun y _ => hg y) hgrad (left_mem_segment ℝ x (x + h)) (right_mem_segment ℝ x (x + h))
  simpa only [add_sub_cancel_left, pow_two, mul_assoc] using! hh

theorem schwartz_hessian_bound_on_short_segment
    (g : 𝓢(Ambient d, F)) (k : ℕ) (x h : Ambient d) (hx : 0 < ‖x‖)
    (hh : ‖h‖ ≤ ‖x‖ / 2) (z : Ambient d) (hz : z ∈ segment ℝ x (x + h)) :
    ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ SchwartzMap.seminorm ℝ k 2 g / (‖x‖ / 2) ^ k := by
  have hzx : ‖z - x‖ ≤ ‖h‖ := by
    simpa only [add_sub_cancel_left] using! norm_sub_le_of_mem_segment hz
  have hnorm := norm_sub_norm_le x z
  rw [norm_sub_rev x z] at hnorm
  have hzlow : ‖x‖ / 2 ≤ ‖z‖ := by linarith
  have hbase : 0 < ‖x‖ / 2 := by positivity
  have he : ‖fderiv ℝ (fderiv ℝ g) z‖ = ‖iteratedFDeriv ℝ 2 g z‖ := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  rw [he]
  apply (le_div_iff₀ (pow_pos hbase k)).2
  calc
    _ = (‖x‖ / 2) ^ k * ‖iteratedFDeriv ℝ 2 g z‖ := mul_comm _ _
    _ ≤ ‖z‖ ^ k * ‖iteratedFDeriv ℝ 2 g z‖ := by gcongr
    _ ≤ _ := le_seminorm ℝ k 2 g z

theorem schwartz_second_difference_spatial_bound
    (g : 𝓢(Ambient d, F)) (k : ℕ) (x h : Ambient d) (hx : 0 < ‖x‖)
    (hh : ‖h‖ ≤ ‖x‖ / 2) :
    ‖symmetricSecondDifference g x h‖ ≤
      2 * (SchwartzMap.seminorm ℝ k 2 g / (‖x‖ / 2) ^ k) * ‖h‖ ^ 2 := by
  let M := SchwartzMap.seminorm ℝ k 2 g / (‖x‖ / 2) ^ k
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hdg : Differentiable ℝ (fderiv ℝ g) :=
    (fderivCLM ℝ (Ambient d) F g).differentiable
  have hp := first_order_remainder_from_segment_hessian g g.differentiable hdg M hM x h
    (schwartz_hessian_bound_on_short_segment g k x h hx hh)
  have hn : ‖-h‖ ≤ ‖x‖ / 2 := by simpa only [norm_neg] using! hh
  have hm := first_order_remainder_from_segment_hessian g g.differentiable hdg M hM x (-h)
    (schwartz_hessian_bound_on_short_segment g k x (-h) hx hn)
  have heq : symmetricSecondDifference g x h =
      (g (x + h) - g x - fderiv ℝ g x h) +
      (g (x + -h) - g x - fderiv ℝ g x (-h)) := by
    simp only [symmetricSecondDifference, map_neg, sub_eq_add_neg, two_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖g (x + h) - g x - fderiv ℝ g x h‖ +
        ‖g (x + -h) - g x - fderiv ℝ g x (-h)‖ := norm_add_le _ _
    _ ≤ M * ‖h‖ ^ 2 + M * ‖-h‖ ^ 2 := add_le_add hp hm
    _ = _ := by rw [norm_neg]; ring

end

end RieszRectifiability

end OAI
