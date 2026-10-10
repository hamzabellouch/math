import Mathlib
import OAI.Analysis.WeakInfiniteness.VectorStates

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

open scoped ComplexOrder InnerProductSpace Topology

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def RepresentationInvariant (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : Submodule ℂ H) : Prop :=
  ∀ a : A,∀ x ∈ S,π a x ∈ S

def RepresentationIrreducible (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  ∀ S : Submodule ℂ H,IsClosed (S : Set H) → RepresentationInvariant π S → S=⊥ ∨ S=⊤

lemma RepresentationInvariant.orthogonal {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)}
    {S : Submodule ℂ H} (hS : RepresentationInvariant π S) :
    RepresentationInvariant π Sᗮ := by
  intro a x hx y hy
  have ho := hx (π (star a) y) (hS (star a) y hy)
  rw [map_star] at ho
  change inner ℂ ((π a).adjoint y) x=0 at ho
  rwa [ContinuousLinearMap.adjoint_inner_left] at ho

lemma RepresentationInvariant.projection_commutes {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)}
    {S : Submodule ℂ H} [S.HasOrthogonalProjection] (hS : RepresentationInvariant π S)
    (a : A) (x : H) : S.starProjection (π a x)= π a (S.starProjection x) := by
  apply S.eq_starProjection_of_mem_orthogonal
  · exact hS a _ (S.starProjection_apply_mem x)
  · rw [← map_sub]
    exact hS.orthogonal a _ (S.sub_starProjection_mem_orthogonal x)

lemma RepresentationInvariant.vectorFunctional_decomposition {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)}
    {S : Submodule ℂ H} [S.HasOrthogonalProjection] (hS : RepresentationInvariant π S)
    (x : H) : representationVectorFunctional π x =
      representationVectorFunctional π (S.starProjection x)+
        representationVectorFunctional π (Sᗮ.starProjection x) := by
  ext b
  change (inner ℂ x (π (b : A) x)).re=
    (inner ℂ (S.starProjection x) (π (b : A) (S.starProjection x))).re+
    (inner ℂ (Sᗮ.starProjection x) (π (b : A) (Sᗮ.starProjection x))).re
  have hxy : inner ℂ (S.starProjection x) (π (b : A) (Sᗮ.starProjection x))=0 :=
    hS.orthogonal (b : A) _ (Sᗮ.starProjection_apply_mem x) _ (S.starProjection_apply_mem x)
  have hyx : inner ℂ (Sᗮ.starProjection x) (π (b : A) (S.starProjection x))=0 :=
    inner_eq_zero_symm.mpr ((Sᗮ.starProjection_apply_mem x) _ (hS (b : A) _ (S.starProjection_apply_mem x)))
  conv_lhs => rw [← S.starProjection_add_starProjection_orthogonal x]
  simp only [map_add,inner_add_left,inner_add_right,hxy,hyx,add_zero,zero_add,Complex.add_re]

variable [PartialOrder A] [StarOrderedRing A]

lemma gnsAction_cyclic_eq (f : A →ₚ[ℂ] ℂ) (a : A) :
    f.gnsStarAlgHom a (gnsCyclicVector f)=(f.toPreGNS a : f.GNS) := by
  change f.gnsNonUnitalStarAlgHom a (f.toPreGNS 1 : f.GNS)=_
  rw [PositiveLinearMap.gnsNonUnitalStarAlgHom_apply_coe]
  change ((f.toPreGNS (a*1)) : f.GNS)=_
  rw [mul_one]

lemma gnsAction_cyclic_dense (f : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a : A => f.gnsStarAlgHom a (gnsCyclicVector f)) := by
  have hr : Set.range (fun a : A => f.gnsStarAlgHom a (gnsCyclicVector f))=
      Set.range (fun a : f.PreGNS => (a : f.GNS)) := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨f.toPreGNS a,(gnsAction_cyclic_eq f a).symm⟩
    · rintro ⟨a,rfl⟩
      refine ⟨f.ofPreGNS a,?_⟩
      change f.gnsStarAlgHom (f.ofPreGNS a) (gnsCyclicVector f)=(a : f.GNS)
      rw [gnsAction_cyclic_eq,PositiveLinearMap.toPreGNS_ofPreGNS]
  change Dense (Set.range _)
  rw [hr]
  exact UniformSpace.Completion.denseRange_coe

end

end WeakPureInfiniteness
end

end OAI
