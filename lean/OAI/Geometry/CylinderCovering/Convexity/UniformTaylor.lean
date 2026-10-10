import Mathlib

namespace OAI

noncomputable section
open Set Metric
open scoped Topology ContDiff
namespace CylinderUniformTaylor

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem remainder_sq_of_lipschitz_fderiv {f : E → F} {S : Set E} {C : NNReal}
    (hf : ∀ z ∈ S, DifferentiableAt ℝ f z)
    (hLip : LipschitzOnWith C (fderiv ℝ f) S)
    {x y : E} (hseg : segment ℝ x y ⊆ S) :
    ‖f y - f x - fderiv ℝ f x (y-x)‖ ≤ (C : ℝ) * ‖y-x‖ ^ 2 := by
  have hx : x ∈ S := hseg (left_mem_segment ℝ x y)
  have hbound : ∀ z ∈ segment ℝ x y,
      ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ (C : ℝ) * ‖y-x‖ := by
    intro z hz
    exact (hLip.norm_sub_le (hseg hz) hx).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) C.2)
  have h := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    (fun z hz => hf z (hseg hz)) hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [pow_two, mul_assoc] using h

theorem remainder_sq_of_hessian_bound {f : E → F} {S : Set E} {C : ℝ}
    (hC : 0 ≤ C) (hS : Convex ℝ S)
    (hf : ∀ z ∈ S, DifferentiableAt ℝ f z)
    (hdf : ∀ z ∈ S, DifferentiableAt ℝ (fderiv ℝ f) z)
    (hbound : ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    ‖f y - f x - fderiv ℝ f x (y-x)‖ ≤ C * ‖y-x‖ ^ 2 := by
  let K : NNReal := ⟨C,hC⟩
  have hLip : LipschitzOnWith K (fderiv ℝ f) S :=
    hS.lipschitzOnWith_of_nnnorm_fderiv_le hdf (fun z hz => hbound z hz)
  exact remainder_sq_of_lipschitz_fderiv hf hLip (hS.segment_subset hx hy)

theorem uniform_remainder_near_compact [ProperSpace E]
    {f : E → F} {D U : Set E} (hD : IsCompact D) (hU : IsOpen U)
    (hDU : D ⊆ U) (hf : ContDiffOn ℝ 2 f U) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x ∈ D, ∀ y : E, ‖y-x‖ ≤ δ →
        ‖f y - f x - fderiv ℝ f x (y-x)‖ ≤ C * ‖y-x‖ ^ 2 := by
  obtain ⟨δ, hδ, hδU⟩ := hD.exists_cthickening_subset_open hU hDU
  have hg : ContDiffOn ℝ 1 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
  have hlocal : LocallyLipschitzOn (cthickening δ D) (fderiv ℝ f) := by
    intro x hx
    have hcx : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
      (hg x (hδU hx)).contDiffAt (hU.mem_nhds (hδU hx))
    obtain ⟨K, t, ht, hKt⟩ := hcx.exists_lipschitzOnWith
    exact ⟨K,t,mem_nhdsWithin_of_mem_nhds ht,hKt⟩
  obtain ⟨K,hK⟩ := hlocal.exists_lipschitzOnWith_of_compact hD.cthickening
  refine ⟨δ,hδ,(K : ℝ)+1,by positivity,?_⟩
  intro x hx y hy
  have hseg : segment ℝ x y ⊆ cthickening δ D := by
    intro z hz
    apply closedBall_subset_cthickening hx δ
    rw [mem_closedBall, dist_eq_norm]
    exact (norm_sub_le_of_mem_segment hz).trans hy
  have hdiff : ∀ z ∈ cthickening δ D, DifferentiableAt ℝ f z := by
    intro z hz
    exact ((hf z (hδU hz)).contDiffAt (hU.mem_nhds (hδU hz))).differentiableAt (by norm_num)
  exact (remainder_sq_of_lipschitz_fderiv hdiff hK hseg).trans
    (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))

theorem planar_square_remainder {f : EuclideanSpace ℝ (Fin 2) → F}
    {x y : EuclideanSpace ℝ (Fin 2)} {δ C : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hcoord : ∀ i : Fin 2, |y i - x i| ≤ δ)
    (hrem : ‖f y - f x - fderiv ℝ f x (y-x)‖ ≤ C * ‖y-x‖ ^ 2) :
    ‖f y - f x - fderiv ℝ f x (y-x)‖ ≤ 2*C*δ^2 := by
  have hnorm : ‖y-x‖ ^ 2 ≤ 2*δ^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two, PiLp.sub_apply]
    have h0 := sq_le_sq₀ (abs_nonneg (y 0-x 0)) hδ |>.mpr (hcoord 0)
    have h1 := sq_le_sq₀ (abs_nonneg (y 1-x 1)) hδ |>.mpr (hcoord 1)
    rw [sq_abs] at h0 h1
    linarith
  calc
    _ ≤ C * ‖y-x‖ ^ 2 := hrem
    _ ≤ C * (2*δ^2) := mul_le_mul_of_nonneg_left hnorm hC
    _ = 2*C*δ^2 := by ring

theorem quadratic_collar_area {δ A : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hA : 0 ≤ A) :
    (δ + A*δ^2)^2 ≤ δ^2 + (2*A+A^2)*δ^3 := by
  have hδsq : δ^2 ≤ δ := by nlinarith
  have hscaled : A * δ^2 ≤ A * δ := mul_le_mul_of_nonneg_left hδsq hA
  nlinarith only [mul_le_mul_of_nonneg_left hscaled (mul_nonneg hA (sq_nonneg δ))]

end CylinderUniformTaylor

end

end OAI
