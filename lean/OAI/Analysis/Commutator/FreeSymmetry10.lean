import Mathlib
import OAI.Analysis.Commutator.FreeBlockTensor
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

namespace Kadison.FreeBlocks

open FreeWordTensor UniformSpace

open scoped ComplexOrder InnerProductSpace

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

include hf in
def pullbackState : FaithfulState D where
  functional :=
    { toLinearMap := t.functional.toLinearMap.comp f.toLinearMap
      monotone' := fun _ _ hab => t.functional.monotone
        ((NonUnitalStarRingHom.ofClass f).map_le_map_of_map_star hab) }
  normalized := by change t.functional (f 1)=1; simpa using t.normalized
  faithful := by
    intro a ha
    apply hf
    rw [map_zero]
    apply t.faithful
    change t.functional (f (star a*a))=0 at ha
    simpa only [map_mul, map_star] using ha

@[simp] lemma pullbackState_apply (a : D) :
    (pullbackState t f hf).functional a = t.functional (f a) := rfl

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i : ι) (hS : S i=f.range)

def factorPreMap : preSpace (pullbackState t f hf) →ₗᵢ[ℂ] factorSpace t S i where
  toLinearMap :=
    { toFun := fun x => ⟨t.functional.toPreGNS (f ((pullbackState t f hf).functional.ofPreGNS x)), by
        change f _ ∈ S i
        rw [hS]
        exact ⟨_,rfl⟩⟩
      map_add' := by intro x y; apply Subtype.ext; simp
      map_smul' := by intro c x; apply Subtype.ext; simp }
  norm_map' x := by
    change ‖t.functional.toPreGNS (f ((pullbackState t f hf).functional.ofPreGNS x))‖ = ‖x‖
    simp only [PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.ofPreGNS_toPreGNS,
      pullbackState_apply, map_mul, map_star]

lemma factorPreMap_surjective : Function.Surjective (factorPreMap t f hf S i hS) := by
  intro y
  have hy : t.functional.ofPreGNS (y : preSpace t) ∈ f.range := hS ▸ y.property
  obtain ⟨x,hx⟩ := hy
  refine ⟨(pullbackState t f hf).functional.toPreGNS x, ?_⟩
  apply Subtype.ext
  change t.functional.toPreGNS (f x)=(y : preSpace t)
  change f x=t.functional.ofPreGNS (y : preSpace t) at hx
  rw [hx, PositiveLinearMap.toPreGNS_ofPreGNS]

def factorPreIso : preSpace (pullbackState t f hf) ≃ₗᵢ[ℂ] factorSpace t S i :=
  LinearIsometryEquiv.ofSurjective (factorPreMap t f hf S i hS)
    (factorPreMap_surjective t f hf S i hS)

def factorGNSIso : Completion (factorSpace t S i) ≃ₗᵢ[ℂ]
    (pullbackState t f hf).functional.GNS :=
  (HilbertCompletion.congr (factorPreIso t f hf S i hS)).symm

@[simp] lemma factorGNSIso_coe (a : D) :
    factorGNSIso t f hf S i hS
      ((⟨t.functional.toPreGNS (f a), by exact (factorPreMap t f hf S i hS
        ((pullbackState t f hf).functional.toPreGNS a)).property⟩ : factorSpace t S i) :
        Completion (factorSpace t S i)) =
      ((pullbackState t f hf).functional.toPreGNS a : (pullbackState t f hf).functional.GNS) := by
  apply (HilbertCompletion.congr (factorPreIso t f hf S i hS)).injective
  simp only [factorGNSIso, LinearIsometryEquiv.apply_symm_apply, HilbertCompletion.congr_coe]
  rfl

end Kadison.FreeBlocks
end

end OAI
