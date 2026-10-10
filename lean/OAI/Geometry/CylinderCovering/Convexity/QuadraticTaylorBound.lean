import Mathlib

namespace OAI

noncomputable section
open Set Metric
open scoped Topology ContDiff
namespace CylinderCovering.QuadraticTaylor

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem remainder_le_on_closedBall {f : E → F} {x y : E} {r M : ℝ}
    (hr : 0 ≤ r) (hM : 0 ≤ M) (hy : y ∈ closedBall x r)
    (hf : ∀ z ∈ closedBall x r, DifferentiableAt ℝ f z)
    (hdf : ∀ z ∈ closedBall x r, DifferentiableAt ℝ (fderiv ℝ f) z)
    (hbound : ∀ z ∈ closedBall x r, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ M) :
    ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ M * r ^ 2 := by
  have hx : x ∈ closedBall x r := mem_closedBall_self hr
  have hder : ∀ z ∈ closedBall x r, ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ M * r := by
    intro z hz
    have hlip := (convex_closedBall x r).norm_image_sub_le_of_norm_fderiv_le hdf hbound hx hz
    have hdist : ‖z - x‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hz
    exact hlip.trans (mul_le_mul_of_nonneg_left hdist hM)
  have hrem := (convex_closedBall x r).norm_image_sub_le_of_norm_fderiv_le' hf hder hx hy
  have hdist : ‖y - x‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hy
  calc
    ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ M * r * ‖y - x‖ := hrem
    _ ≤ M * r * r := mul_le_mul_of_nonneg_left hdist (mul_nonneg hM hr)
    _ = M * r ^ 2 := by ring

theorem exists_uniform_taylor_bound_of_bounded_hessian {f : E → F} {D U : Set E}
    {B : ℝ} (hD : IsCompact D) (hU : IsOpen U) (hDU : D ⊆ U) (hB : 0 ≤ B)
    (hf : ∀ z ∈ U, DifferentiableAt ℝ f z)
    (hdf : ∀ z ∈ U, DifferentiableAt ℝ (fderiv ℝ f) z)
    (hbound : ∀ z ∈ U, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ B) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ D, ∀ y : E, ‖y - x‖ ≤ r →
      ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ B * ‖y - x‖ ^ 2 := by
  obtain ⟨r, hr, hrU⟩ := hD.exists_cthickening_subset_open hU hDU
  refine ⟨r, hr, ?_⟩
  intro x hx y hy
  have hball : closedBall x ‖y - x‖ ⊆ U :=
    (closedBall_subset_cthickening hx ‖y - x‖).trans
      ((cthickening_mono hy D).trans hrU)
  exact remainder_le_on_closedBall (norm_nonneg _) hB
    (by simp only [mem_closedBall, dist_eq_norm, le_refl])
    (fun z hz => hf z (hball hz)) (fun z hz => hdf z (hball hz))
    (fun z hz => hbound z (hball hz))

theorem exists_uniform_taylor_bound [ProperSpace E] {f : E → F} {D U : Set E}
    (hD : IsCompact D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hf : ContDiffOn ℝ 2 f U) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ r → ∀ x ∈ D, ∀ y ∈ closedBall x δ,
        ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ M * δ ^ 2 := by
  obtain ⟨r, hr, hrU⟩ := hD.exists_cthickening_subset_open hU hDU
  have hf1 : ContDiffOn ℝ 1 (fderiv ℝ f) U :=
    hf.fderiv_of_isOpen hU (by norm_num)
  have hf2 : ContinuousOn (fderiv ℝ (fderiv ℝ f)) U :=
    (hf1.fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn
  obtain ⟨B, hB⟩ := (hD.cthickening (r := r)).exists_bound_of_continuousOn
    (E := E →L[ℝ] E →L[ℝ] F) (hf2.mono hrU)
  refine ⟨r, max B 1, hr, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _), ?_⟩
  intro δ hδ hδr x hx y hy
  have hball : closedBall x δ ⊆ cthickening r D :=
    (closedBall_subset_cthickening hx δ).trans (cthickening_mono hδr D)
  apply remainder_le_on_closedBall hδ (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right B 1)) hy
  · intro z hz
    exact (hf.contDiffAt (hU.mem_nhds (hrU (hball hz)))).differentiableAt (by norm_num)
  · intro z hz
    exact (hf1.contDiffAt (hU.mem_nhds (hrU (hball hz)))).differentiableAt (by norm_num)
  · intro z hz
    exact (hB z (hball hz)).trans (le_max_left B 1)

theorem exists_uniform_taylor_bound_near [ProperSpace E] {f : E → F} {D : Set E}
    (hD : IsCompact D)
    (hf : ∃ U : Set E, IsOpen U ∧ D ⊆ U ∧ ContDiffOn ℝ 2 f U) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ r → ∀ x ∈ D, ∀ y ∈ closedBall x δ,
        ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ M * δ ^ 2 := by
  obtain ⟨U, hU, hDU, hfU⟩ := hf
  exact exists_uniform_taylor_bound hD hU hDU hfU

theorem exists_uniform_taylor_norm_bound_near [ProperSpace E] {f : E → F} {D : Set E}
    (hD : IsCompact D)
    (hf : ∃ U : Set E, IsOpen U ∧ D ⊆ U ∧ ContDiffOn ℝ 2 f U) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧ ∀ x ∈ D, ∀ y : E, ‖y - x‖ ≤ r →
        ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ M * ‖y - x‖ ^ 2 := by
  obtain ⟨r, M, hr, hM, hbound⟩ := exists_uniform_taylor_bound_near hD hf
  refine ⟨r, M, hr, hM, ?_⟩
  intro x hx y hy
  exact hbound ‖y - x‖ (norm_nonneg _) hy x hx y (by simp [mem_closedBall, dist_eq_norm])

end CylinderCovering.QuadraticTaylor

end

end OAI
