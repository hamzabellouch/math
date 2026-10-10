import OAI.Geometry.SurfaceImmersion.Whitney.TransverseRuledSurface

namespace OAI

/-! Quantitative bounds for a remainder vanishing to first order on the axis. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma axis_projection_norm_le (x : Base) : ‖crosscapAxis (x 1)‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  fin_cases i
  · simp [crosscapAxis_apply]
  · simpa [crosscapAxis_apply] using norm_le_pi_norm x (1 : Fin 2)

lemma norm_axis_difference (x : Base) : ‖x-crosscapAxis (x 1)‖ = |x 0| := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (abs_nonneg (x 0))).mpr
    intro i
    fin_cases i <;> simp [crosscapAxis_apply]
  · simpa [crosscapAxis_apply] using norm_le_pi_norm (x-crosscapAxis (x 1)) (0 : Fin 2)

lemma axis_flat_first_bound {R : Base → V} (hR : ContDiff ℝ ∞ R)
    (hD0 : ∀ t, fderiv ℝ R (crosscapAxis t) = 0)
    {ρ C : ℝ} (hb : ∀ x ∈ closedBall (0 : Base) ρ, ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ C)
    {x : Base} (hx : x ∈ closedBall (0 : Base) ρ) :
    ‖fderiv ℝ R x‖ ≤ C*|x 0| := by
  have ha : crosscapAxis (x 1) ∈ closedBall (0 : Base) ρ := by
    rw [mem_closedBall,dist_zero_right]
    exact (axis_projection_norm_le x).trans (by simpa only [mem_closedBall,dist_zero_right] using hx)
  have h := (convex_closedBall (0 : Base) ρ).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => (hR.fderiv_right (m := ∞) (by simp)).differentiable (by simp) y) hb ha hx
  simpa only [hD0,sub_zero,norm_axis_difference] using h

lemma axis_flat_value_bound {R : Base → V} (hR : ContDiff ℝ ∞ R)
    (h0 : ∀ t, R (crosscapAxis t) = 0) (hD0 : ∀ t, fderiv ℝ R (crosscapAxis t) = 0)
    {ρ C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x ∈ closedBall (0 : Base) ρ, ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ C)
    {x : Base} (hx : x ∈ closedBall (0 : Base) ρ) : ‖R x‖ ≤ C*|x 0|^2 := by
  let a := crosscapAxis (x 1)
  let S := closedBall (0 : Base) ρ ∩ closedBall a |x 0|
  have haρ : a ∈ closedBall (0 : Base) ρ := by
    rw [mem_closedBall,dist_zero_right]
    exact (axis_projection_norm_le x).trans (by simpa only [mem_closedBall,dist_zero_right] using hx)
  have haS : a ∈ S := ⟨haρ,mem_closedBall_self (abs_nonneg _)⟩
  have hxS : x ∈ S := ⟨hx,by rw [mem_closedBall,dist_eq_norm,norm_axis_difference]⟩
  have hDS : ∀ y ∈ S, ‖fderiv ℝ R y‖ ≤ C*|x 0| := by
    intro y hy
    apply (axis_flat_first_bound hR hD0 hb hy.1).trans
    apply mul_le_mul_of_nonneg_left _ hC
    have hcoord := norm_le_pi_norm (y-a) (0 : Fin 2)
    have ha0 : a 0 = 0 := by simp [a,crosscapAxis_apply]
    have hcoord' : |y 0| ≤ ‖y-a‖ := by simpa only [Pi.sub_apply,ha0,sub_zero,Real.norm_eq_abs] using hcoord
    exact hcoord'.trans (by simpa only [mem_closedBall,dist_eq_norm] using hy.2)
  have h := ((convex_closedBall (0 : Base) ρ).inter (convex_closedBall a |x 0|)).norm_image_sub_le_of_norm_fderiv_le (fun y _ => hR.differentiable (by simp) y) hDS haS hxS
  have h' : ‖R x‖ ≤ C*|x 0| * |x 0| := by
    simpa only [a,h0,sub_zero,norm_axis_difference] using h
  nlinarith only [h']

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
