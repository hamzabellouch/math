import Mathlib
import OAI.Analysis.Commutator.TensorCompletion

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace

namespace Kadison.HilbertCompletion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def completeEquiv [CompleteSpace E] : E ≃ₗᵢ[ℂ] Completion E :=
  LinearIsometryEquiv.ofSurjective (coeIsometry E) (by
    intro x
    induction x using Completion.induction_on with
    | hp => exact (coeIsometry E).isometry.isClosedEmbedding.isClosed_range
    | ih x => exact ⟨x,rfl⟩)

@[simp] lemma completeEquiv_apply [CompleteSpace E] (x : E) :
    completeEquiv x=(x : Completion E) := rfl

abbrev centered (Ω : E) : Submodule ℂ E := (ℂ ∙ Ω)ᗮ

def centeredMap (Ω : E) : Completion (centered Ω) →ₗᵢ[ℂ]
    centered (Ω : Completion E) where
  toLinearMap := (map (centered Ω).subtypeₗᵢ).toLinearMap.codRestrict _ (by
    intro x
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    change inner ℂ (Ω : Completion E) (map (centered Ω).subtypeₗᵢ x)=0
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x =>
      rw [map_coe, Completion.inner_coe]
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property)
  norm_map' x := (map (centered Ω).subtypeₗᵢ).norm_map x

@[simp] lemma centeredMap_coe (Ω : E) (x : centered Ω) :
    (centeredMap Ω (x : Completion (centered Ω)) : Completion E) =
      ((x : E) : Completion E) := map_coe _ _

lemma centeredMap_surjective (Ω : E) (hΩ : ‖Ω‖=1) :
    Function.Surjective (centeredMap Ω) := by
  let Q := centered (Ω : Completion E)
  let R : Submodule ℂ Q := LinearMap.range (centeredMap Ω).toLinearMap
  have hR : IsClosed (R : Set Q) := (centeredMap Ω).isometry.isClosedEmbedding.isClosed_range
  have hc : ∀ x : E, Q.orthogonalProjectionOnto (x : Completion E) ∈ R := by
    intro x
    let y : centered Ω := ⟨x-inner ℂ Ω x • Ω, by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, inner_smul_right,
        inner_self_eq_norm_sq_to_K, hΩ]
      simp⟩
    refine ⟨(y : Completion (centered Ω)), ?_⟩
    apply Subtype.ext
    change (centeredMap Ω (y : Completion (centered Ω)) : Completion E) = _
    rw [centeredMap_coe]
    change ((x-inner ℂ Ω x • Ω : E) : Completion E) =
      (ℂ ∙ (Ω : Completion E))ᗮ.starProjection (x : Completion E)
    rw [Submodule.starProjection_orthogonal_val,
      Submodule.starProjection_unit_singleton ℂ (by simpa), Completion.coe_sub,
      Completion.coe_smul, Completion.inner_coe]
  have hd : DenseRange (fun x : E => Q.orthogonalProjectionOnto (x : Completion E)) := by
    apply (show Function.Surjective Q.orthogonalProjectionOnto from fun x =>
      ⟨x, Q.orthogonalProjectionOnto_mem_subspace_eq_self x⟩).denseRange.comp
      Completion.denseRange_coe Q.orthogonalProjectionOnto.continuous
  intro x
  change x ∈ R
  exact hR.closure_subset_iff.mpr (Set.range_subset_iff.mpr hc) (hd x)

def centeredEquiv (Ω : E) (hΩ : ‖Ω‖=1) : Completion (centered Ω) ≃ₗᵢ[ℂ]
    centered (Ω : Completion E) :=
  LinearIsometryEquiv.ofSurjective (centeredMap Ω) (centeredMap_surjective Ω hΩ)

end Kadison.HilbertCompletion
end

end OAI
