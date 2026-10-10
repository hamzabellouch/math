import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma first_order_remainder_le_of_hessian_bound {f : E → ℝ} {S : Set E}
    (hS : Convex ℝ S) {B : ℝ} (hB : 0≤B)
    (hf : ∀ z∈S, ContDiffAt ℝ 2 f z)
    (hbound : ∀ z∈S, ‖fderiv ℝ (fderiv ℝ f) z‖≤B)
    {x y : E} (hx : x∈S) (hy : y∈S) :
    |f y-f x-fderiv ℝ f x (y-x)|≤B*‖y-x‖^2 := by
  have hD : ∀ z∈S, HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z := by
    intro z hz
    exact ((hf z hz).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt
  have hLip : ∀ z∈S, ‖fderiv ℝ f z-fderiv ℝ f x‖≤B*‖z-x‖ := by
    intro z hz
    exact hS.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun w hw => (hD w hw).hasFDerivWithinAt) hbound hx hz
  let R := fun z => f z-f x-fderiv ℝ f x (z-x)
  have hR : ∀ z∈S, HasFDerivAt R (fderiv ℝ f z-fderiv ℝ f x) z := by
    intro z hz
    exact ((hf z hz).differentiableAt (by norm_num)).hasFDerivAt.sub_const (f x) |>.sub
      ((fderiv ℝ f x).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x))
  have hseg : segment ℝ x y ⊆ S := hS.segment_subset hx hy
  have hn : ∀ z∈segment ℝ x y, ‖z-x‖≤‖y-x‖ := by
    intro z hz
    simpa only [Metric.mem_closedBall,dist_eq_norm] using
      (show segment ℝ x y ⊆ Metric.closedBall x ‖y-x‖ from
      (convex_closedBall x ‖y-x‖).segment_subset
        (Metric.mem_closedBall_self (norm_nonneg _)) (by simp only [Metric.mem_closedBall,dist_eq_norm,le_refl])) hz
  have H := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hR z (hseg hz)).hasFDerivWithinAt)
    (show ∀ z∈segment ℝ x y, ‖fderiv ℝ f z-fderiv ℝ f x‖≤B*‖y-x‖ from by
      intro z hz
      exact (hLip z (hseg hz)).trans (mul_le_mul_of_nonneg_left (hn z hz) hB))
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [R,sub_self,map_zero,sub_zero,Real.norm_eq_abs,pow_two,mul_assoc] using H

lemma convexOn_of_affine_lower_supports {f : E → ℝ} {S : Set E}
    (hS : Convex ℝ S)
    (hs : ∀ x∈S, ∃ L : E →L[ℝ] ℝ, ∀ y∈S, f x+L (y-x)≤f y) :
    ConvexOn ℝ S f := by
  refine ⟨hS,?_⟩
  intro x hx y hy a b ha hb hab
  let z := a • x+b • y
  obtain ⟨L,hL⟩ := hs z (hS hx hy ha hb hab)
  have hx' := mul_le_mul_of_nonneg_left (hL x hx) ha
  have hy' := mul_le_mul_of_nonneg_left (hL y hy) hb
  have hzero : a*L (x-z)+b*L (y-z)=0 := by
    rw [←smul_eq_mul a,←smul_eq_mul b,←map_smul,←map_smul,←map_add]
    have he : a • (x-z)+b • (y-z)=0 := by
      rw [smul_sub,smul_sub,←add_sub_add_comm,←add_smul,hab,one_smul]
      exact sub_self z
    rw [he,map_zero]
  change f z≤a*f x+b*f y
  have hc : a*f z+b*f z=f z := by rw [←add_mul,hab,one_mul]
  nlinarith [hc]

end WeakMTWTransport
end

end OAI
