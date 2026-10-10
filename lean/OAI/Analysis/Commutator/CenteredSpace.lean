import Mathlib

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace

namespace Kadison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

abbrev centeredSpace (Ω : E) : Submodule ℂ E := (ℂ ∙ Ω)ᗮ

def center (Ω : E) : E →L[ℂ] centeredSpace Ω :=
  (centeredSpace Ω).orthogonalProjectionOnto

lemma norm_center_le (Ω x : E) : ‖center Ω x‖ ≤ ‖x‖ :=
  (centeredSpace Ω).norm_orthogonalProjectionOnto_apply_le x

lemma coe_center (Ω : E) (hΩ : ‖Ω‖ = 1) (x : E) :
    (center Ω x : E) = x - inner ℂ Ω x • Ω := by
  change (ℂ ∙ Ω)ᗮ.starProjection x = _
  rw [Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℂ hΩ]

lemma center_vacuum (Ω : E) : center Ω Ω = 0 := by
  apply Subtype.ext
  change (ℂ ∙ Ω)ᗮ.starProjection Ω = (0 : E)
  exact Submodule.starProjection_orthogonalComplement_singleton_eq_zero Ω

lemma center_centered (Ω : E) (x : centeredSpace Ω) : center Ω (x : E) = x :=
  (centeredSpace Ω).orthogonalProjectionOnto_mem_subspace_eq_self x

lemma denseRange_center {M : Type*} [TopologicalSpace M] (Ω : E) (v : M → E)
    (hv : DenseRange v) : DenseRange (fun a => center Ω (v a)) := by
  have hc : Function.Surjective (center Ω) := fun x => ⟨x, center_centered Ω x⟩
  exact hc.denseRange.comp hv (center Ω).continuous

lemma center_isometry (Ω : E) (hΩ : ‖Ω‖ = 1) (U : E →ₗᵢ[ℂ] E) (hU : U Ω = Ω)
    (x : E) : U (center Ω x : E) = (center Ω (U x) : E) := by
  rw [coe_center Ω hΩ, coe_center Ω hΩ, map_sub, map_smul, hU]
  congr 2
  have h := U.inner_map_map Ω x
  rw [hU] at h
  exact h.symm

def centeredIsometry (Ω : E) (U : E →ₗᵢ[ℂ] E) (hU : U Ω = Ω) :
    centeredSpace Ω →ₗᵢ[ℂ] centeredSpace Ω :=
  { U.toLinearMap.domRestrict (centeredSpace Ω) |>.codRestrict (centeredSpace Ω)
      (fun x => by
        change U (x : E) ∈ (ℂ ∙ Ω)ᗮ
        rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
        have h := U.inner_map_map Ω (x : E)
        rw [hU] at h
        rw [h]
        exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property) with
    norm_map' := fun x => U.norm_map x }

@[simp] lemma centeredIsometry_apply (Ω : E) (U : E →ₗᵢ[ℂ] E) (hU : U Ω = Ω)
    (x : centeredSpace Ω) : (centeredIsometry Ω U hU x : E) = U (x : E) := rfl

lemma centeredIsometry_center (Ω : E) (hΩ : ‖Ω‖ = 1)
    (U : E →ₗᵢ[ℂ] E) (hU : U Ω = Ω) (x : E) :
    centeredIsometry Ω U hU (center Ω x) = center Ω (U x) := by
  apply Subtype.ext
  exact center_isometry Ω hΩ U hU x

end Kadison
end

end OAI
