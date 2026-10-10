import Mathlib

namespace OAI

section

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma convexOn_of_linear_lower_support {u : E → ℝ} {S : Set E}
    (hS : Convex ℝ S)
    (h : ∀ x∈S, ∃ l : E →L[ℝ] ℝ, ∀ y∈S, u x+l (y-x) ≤ u y) :
    ConvexOn ℝ S u := by
  refine ⟨hS,?_⟩
  intro x hx y hy a b ha hb hab
  obtain ⟨l,hl⟩ := h (a • x+b • y) (hS hx hy ha hb hab)
  have H₁ := mul_le_mul_of_nonneg_left (hl x hx) ha
  have H₂ := mul_le_mul_of_nonneg_left (hl y hy) hb
  have he : a*l (x-(a • x+b • y))+b*l (y-(a • x+b • y)) = 0 := by
    change a • l (x-(a • x+b • y))+b • l (y-(a • x+b • y)) = 0
    rw [← map_smul,← map_smul,← map_add]
    have hz : a • (x-(a • x+b • y))+b • (y-(a • x+b • y)) = 0 := by
      rw [smul_sub,smul_sub]
      calc
        _ = (a • x+b • y)-(a • (a • x+b • y)+b • (a • x+b • y)) := by abel
        _ = 0 := by rw [← add_smul,hab,one_smul,sub_self]
    rw [hz,map_zero]
  simp only [smul_eq_mul]
  have habu := congrArg (fun t : ℝ => t * u (a • x+b • y)) hab
  nlinarith only [H₁,H₂,he,habu]

lemma convexOn_of_quadratic_lower_support {u : E → ℝ} {S : Set E} {K : ℝ}
    (hS : Convex ℝ S)
    (h : ∀ x∈S, ∃ l : E →L[ℝ] ℝ, ∀ y∈S, u x+l (y-x)-K*‖y-x‖^2 ≤ u y) :
    ConvexOn ℝ S (fun z => u z+K*‖z‖^2) := by
  apply convexOn_of_linear_lower_support hS
  intro x hx
  obtain ⟨l,hl⟩ := h x hx
  refine ⟨l+(2*K) • innerSL ℝ x,?_⟩
  intro y hy
  have H := hl y hy
  have hn : ‖y‖^2-‖x‖^2-2*inner ℝ x (y-x)=‖y-x‖^2 := by
    simp only [← real_inner_self_eq_norm_sq,inner_sub_left,inner_sub_right,real_inner_comm y x]
    ring
  simp only [add_apply,smul_apply,innerSL_apply_apply,smul_eq_mul]
  have hnK := congrArg (fun t : ℝ => K*t) hn
  nlinarith only [H,hnK]

end
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma c2_quadratic_remainder_on_convex {f : E → ℝ} {S : Set E} {K : ℝ}
    (hK : 0≤K) (hS : Convex ℝ S) (hf : ∀ z∈S, ContDiffAt ℝ 2 f z)
    (hbound : ∀ z∈S, ‖fderiv ℝ (fderiv ℝ f) z‖≤K) {x y : E} (hx : x∈S) (hy : y∈S) :
    ‖f y-f x-fderiv ℝ f x (y-x)‖ ≤ K*‖y-x‖^2 := by
  have hd (z) (hz : z∈S) : DifferentiableAt ℝ (fderiv ℝ f) z :=
    ((hf z hz).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hseg : segment ℝ x y ⊆ S := hS.segment_subset hx hy
  have hball : segment ℝ x y ⊆ Metric.closedBall x ‖y-x‖ :=
    (convex_closedBall x ‖y-x‖).segment_subset (by simp only [Metric.mem_closedBall,dist_self]; positivity)
      (by simp only [Metric.mem_closedBall,dist_eq_norm,le_refl])
  have hdif (z) (hz : z∈segment ℝ x y) : ‖fderiv ℝ f z-fderiv ℝ f x‖≤K*‖y-x‖ := by
    calc
      _ ≤ K*‖z-x‖ := hS.norm_image_sub_le_of_norm_fderiv_le hd hbound hx (hseg hz)
      _ ≤ K*‖y-x‖ := mul_le_mul_of_nonneg_left (by
        simpa only [Metric.mem_closedBall,dist_eq_norm] using hball hz) hK
  have H := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    (fun z hz => (hf z (hseg hz)).differentiableAt (by norm_num)) hdif
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [mul_assoc,← sq] using H

end
end WeakMTWTransport

end

end

end

end OAI
