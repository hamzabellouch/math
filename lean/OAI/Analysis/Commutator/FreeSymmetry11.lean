import Mathlib
import OAI.Analysis.Commutator.CompletionCentered
import OAI.Analysis.Commutator.FreeSymmetry10

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

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i : ι) (hS : S i=f.range)

lemma inner_pre_one (x : preSpace (pullbackState t f hf)) :
    inner ℂ ((pullbackState t f hf).functional.toPreGNS 1) x =
      (pullbackState t f hf).functional ((pullbackState t f hf).functional.ofPreGNS x) := by
  simp only [PositiveLinearMap.preGNS_inner_def, PositiveLinearMap.ofPreGNS_toPreGNS,
    star_one, one_mul]

def letterPreMap :
    HilbertCompletion.centered ((pullbackState t f hf).functional.toPreGNS 1) →ₗᵢ[ℂ]
      letterSpace t S i where
  toLinearMap :=
    { toFun := fun x => ⟨factorPreMap t f hf S i hS (x : preSpace (pullbackState t f hf)),
        (factorPreMap t f hf S i hS (x : preSpace (pullbackState t f hf))).property, by
          have hx := Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
          rw [inner_pre_one] at hx
          exact hx⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact congrArg (fun z : factorSpace t S i => (z : preSpace t))
          ((factorPreMap t f hf S i hS).map_add
            (x : preSpace (pullbackState t f hf)) (y : preSpace (pullbackState t f hf)))
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact congrArg (fun z : factorSpace t S i => (z : preSpace t))
          ((factorPreMap t f hf S i hS).map_smul c (x : preSpace (pullbackState t f hf))) }
  norm_map' x := (factorPreMap t f hf S i hS).norm_map x

lemma letterPreMap_surjective : Function.Surjective (letterPreMap t f hf S i hS) := by
  intro y
  obtain ⟨x,hx⟩ := factorPreMap_surjective t f hf S i hS ⟨y,y.property.1⟩
  have hx0 : (pullbackState t f hf).functional ((pullbackState t f hf).functional.ofPreGNS x)=0 := by
    have hx' := congrArg (fun z : factorSpace t S i => t.functional (t.functional.ofPreGNS z)) hx
    exact hx'.trans y.property.2
  refine ⟨⟨x,?_⟩,?_⟩
  · rwa [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_pre_one]
  · apply Subtype.ext
    change ((factorPreMap t f hf S i hS) x : preSpace t)=(y : preSpace t)
    exact congrArg (fun z : factorSpace t S i => (z : preSpace t)) hx

def letterPreIso : HilbertCompletion.centered ((pullbackState t f hf).functional.toPreGNS 1) ≃ₗᵢ[ℂ]
    letterSpace t S i :=
  LinearIsometryEquiv.ofSurjective (letterPreMap t f hf S i hS)
    (letterPreMap_surjective t f hf S i hS)

lemma pullback_pre_one_norm : ‖(pullbackState t f hf).functional.toPreGNS 1‖=1 := by
  rw [PositiveLinearMap.preGNS_norm_def]
  simp [map_one, t.normalized]

def letterGNSIso : Completion (letterSpace t S i) ≃ₗᵢ[ℂ]
    HilbertCompletion.centered
      (((pullbackState t f hf).functional.toPreGNS 1 : preSpace (pullbackState t f hf)) :
        (pullbackState t f hf).functional.GNS) :=
  (HilbertCompletion.congr (letterPreIso t f hf S i hS)).symm |>.trans
    (HilbertCompletion.centeredEquiv _ (pullback_pre_one_norm t f hf))

end Kadison.FreeBlocks
end

end OAI
