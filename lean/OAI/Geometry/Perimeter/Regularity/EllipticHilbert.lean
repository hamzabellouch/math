import Mathlib

namespace OAI

noncomputable section
open Set
open scoped InnerProductSpace
namespace RPISingularHarnack

theorem projection_eq_of_pairing_eq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    {u e : H} (h : ∀ w∈K, inner ℝ u w=inner ℝ e w) :
    K.orthogonalProjectionOnto u=K.orthogonalProjectionOnto e := by
  apply ext_inner_right ℝ
  intro w
  simp only [K.inner_orthogonalProjectionOnto_eq_of_mem_right]
  exact h w w.property

theorem harmonic_projection_error_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    {u e : H} (h : ∀ w∈K, inner ℝ u w=inner ℝ e w) :
    ‖u-(u-K.starProjection u)‖≤‖e‖ := by
  rw [sub_sub_cancel,Submodule.starProjection_apply,
    projection_eq_of_pairing_eq K h,Submodule.norm_coe]
  exact K.norm_orthogonalProjectionOnto_apply_le e

theorem harmonic_projection_exists {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    {u e : H} (h : ∀ w∈K, inner ℝ u w=inner ℝ e w) :
    ∃ g : H, g∈Kᗮ ∧ u-g∈K ∧ ‖u-g‖≤‖e‖ := by
  refine ⟨u-K.starProjection u,K.sub_starProjection_mem_orthogonal u,?_,
    harmonic_projection_error_le K h⟩
  rw [sub_sub_cancel]
  exact (K.orthogonalProjectionOnto u).property

end RPISingularHarnack

end

end OAI
