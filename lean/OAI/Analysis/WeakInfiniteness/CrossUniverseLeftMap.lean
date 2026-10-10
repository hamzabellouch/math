import Mathlib
import OAI.Analysis.WeakInfiniteness.CrossUniverseTensorLaws

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

def minimalMapLeftAny (φ : A →⋆ₙₐ[ℂ] B) : MinimalTensor A C →⋆ₙₐ[ℂ] MinimalTensor B C :=
  minimalMapAny φ (NonUnitalStarAlgHom.id ℂ C)

@[simp] lemma minimalMapLeftAny_elementary (φ : A →⋆ₙₐ[ℂ] B) (a : A) (c : C) :
    minimalMapLeftAny φ (minimalElementary a c)=minimalElementary (φ a) c :=
  minimalMapAny_elementary _ _ _ _

lemma norm_minimalMapLeftAny (φ : A →⋆ₙₐ[ℂ] B) (hφ : Function.Injective φ)
    (z : MinimalTensor A C) : ‖minimalMapLeftAny φ z‖=‖z‖ :=
  norm_minimalMapAny φ _ hφ Function.injective_id z

lemma minimalMapLeftAny_tensorCut {A : Type u} {B : Type v}
    [CStarAlgebra A] [CStarAlgebra B] (φ : A →⋆ₐ[ℂ] B) (e : C)
    (x : MinimalTensor A C) :
    minimalMapLeftAny φ.toNonUnitalStarAlgHom (tensorCut e x)=
      tensorCut e (minimalMapLeftAny φ.toNonUnitalStarAlgHom x) := by
  simp only [tensorCut,map_sub,map_mul]
  congr 2
  change minimalMapLeftAny φ.toNonUnitalStarAlgHom (minimalElementary (1:A) e)=minimalElementary (1:B) e
  rw [minimalMapLeftAny_elementary]
  change minimalElementary (φ 1) e=_
  rw [map_one]

lemma minimalMapLeftAny_right_comm {D : Type w} [NonUnitalCStarAlgebra D]
    (φ : A →⋆ₙₐ[ℂ] B) (q : C →⋆ₙₐ[ℂ] D) :
    (minimalMapAny (NonUnitalStarAlgHom.id ℂ B) q).comp (minimalMapLeftAny φ)=
      (minimalMapLeftAny φ).comp (minimalMapAny (NonUnitalStarAlgHom.id ℂ A) q) := by
  apply minimalTensor_hom_ext
  intro a c
  simp [minimalMapLeftAny]

end

end WeakPureInfiniteness
end

end OAI
