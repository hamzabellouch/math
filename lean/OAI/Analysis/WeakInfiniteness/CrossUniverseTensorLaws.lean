import Mathlib
import OAI.Analysis.WeakInfiniteness.CrossUniverseTensorMap
import OAI.Analysis.WeakInfiniteness.WordTensorDensity

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

open scoped TensorProduct ENNReal

open UniformSpace Topology

universe u v w x y z

section

variable {A : Type u} {B : Type v} {C : Type w} {D : Type x}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

lemma minimalTensor_hom_ext {E : Type*} [NonUnitalCStarAlgebra E]
    (f g : MinimalTensor A C →⋆ₙₐ[ℂ] E)
    (h : ∀ a c, f (minimalElementary a c)=g (minimalElementary a c)) : f=g := by
  let S : Submodule ℂ (MinimalTensor A C) :=
    { carrier := {x | f x=g x}
      zero_mem' := by simp
      add_mem' := by intro a b ha hb; simp only [Set.mem_ofPred_eq,map_add] at *; rw [ha,hb]
      smul_mem' := by intro t a ha; simp only [Set.mem_ofPred_eq,map_smul] at *; rw [ha] }
  have hS : S=⊤ := minimal_elementary_span_dense S
    (isClosed_eq (nonUnitalStarHom_continuous f) (nonUnitalStarHom_continuous g)) h
  ext a
  have ha : a ∈ S := by rw [hS]; trivial
  exact ha

@[simp] lemma minimalMapAny_id :
    minimalMapAny (NonUnitalStarAlgHom.id ℂ A) (NonUnitalStarAlgHom.id ℂ C)=
      NonUnitalStarAlgHom.id ℂ (MinimalTensor A C) := by
  apply minimalTensor_hom_ext
  intro a c
  simp

lemma minimalMapAny_comp {E : Type y} {F : Type z}
    [NonUnitalCStarAlgebra E] [NonUnitalCStarAlgebra F]
    (φ : A →⋆ₙₐ[ℂ] B) (ψ : C →⋆ₙₐ[ℂ] D)
    (η : B →⋆ₙₐ[ℂ] E) (κ : D →⋆ₙₐ[ℂ] F) :
    (minimalMapAny η κ).comp (minimalMapAny φ ψ)=minimalMapAny (η.comp φ) (κ.comp ψ) := by
  apply minimalTensor_hom_ext
  intro a c
  simp

lemma norm_spatialSum_le_image_any {ι : Type*} (s : Finset ι) (a : ι → A) (c : ι → C)
    (φ : A →⋆ₙₐ[ℂ] B) (ψ : C →⋆ₙₐ[ℂ] D)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) :
    ‖∑ i ∈ s,spatialElementary (a i) (c i)‖ ≤
      ‖∑ i ∈ s,spatialElementary (φ (a i)) (ψ (c i))‖ := by
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  let := CStarAlgebra.spectralOrder C
  let := CStarAlgebra.spectralOrderedRing C
  let := CStarAlgebra.spectralOrder B
  let := CStarAlgebra.spectralOrderedRing B
  let := CStarAlgebra.spectralOrder D
  let := CStarAlgebra.spectralOrderedRing D
  obtain ⟨H,π,hπ⟩ := exists_faithful_representation B
  obtain ⟨K,ρ,hρ⟩ := exists_faithful_representation D
  apply lp.norm_le_of_forall_le (norm_nonneg _)
  intro σ
  rw [spatialSum_apply,norm_completion]
  calc
    _ ≤ ‖∑ i ∈ s,TensorProduct.mapL (σ.leftRep (a i)) (ρ (ψ (c i)))‖ :=
      tensor_norm_le_faithful_finset s (fun i => σ.leftRep (a i)) c
        (ρ.comp ψ) σ.rightRep (hρ.comp hψ)
    _ = ‖∑ i ∈ s,TensorProduct.mapL (ρ (ψ (c i))) (σ.leftRep (a i))‖ := norm_tensorSum_flip s _ _
    _ ≤ ‖∑ i ∈ s,TensorProduct.mapL (ρ (ψ (c i))) (π (φ (a i)))‖ :=
      tensor_norm_le_faithful_finset s (fun i => ρ (ψ (c i))) a
        (π.comp φ) σ.leftRep (hπ.comp hφ)
    _ = ‖∑ i ∈ s,TensorProduct.mapL (π (φ (a i))) (ρ (ψ (c i)))‖ := norm_tensorSum_flip s _ _
    _ ≤ _ := norm_tensorSum_le_spatial_any s (fun i => φ (a i)) (fun i => ψ (c i)) π ρ

lemma norm_minimalMapAny (φ : A →⋆ₙₐ[ℂ] B) (ψ : C →⋆ₙₐ[ℂ] D)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) (z : MinimalTensor A C) :
    ‖minimalMapAny φ ψ z‖=‖z‖ := by
  apply le_antisymm (NonUnitalStarAlgHom.norm_apply_le _ _)
  let S := Submodule.span ℂ (Set.range fun p : A × C => minimalElementary p.1 p.2)
  have hd : S.topologicalClosure=⊤ := by
    apply minimal_elementary_span_dense _ (Submodule.isClosed_topologicalClosure _)
    intro a c
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self (a,c)))
  have hz : z ∈ closure (S : Set (MinimalTensor A C)) := by
    change z ∈ S.topologicalClosure
    rw [hd]
    trivial
  apply closure_minimal (t := {z | ‖z‖ ≤ ‖minimalMapAny φ ψ z‖}) ?_
    (isClosed_le continuous_norm ((nonUnitalStarHom_continuous _).norm)) hz
  intro z hz
  classical
  obtain ⟨d,rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hz
  change ‖d.sum (fun p t => t • minimalElementary p.1 p.2)‖ ≤
    ‖minimalMapAny φ ψ (d.sum (fun p t => t • minimalElementary p.1 p.2))‖
  simp only [Finsupp.sum,map_sum,map_smul,minimalMapAny_elementary]
  change ‖(minimalTensorSubalgebra A C).subtype (∑ p ∈ d.support,d p • minimalElementary p.1 p.2)‖ ≤
    ‖(minimalTensorSubalgebra B D).subtype (∑ p ∈ d.support,d p • minimalElementary (φ p.1) (ψ p.2))‖
  simp only [map_sum,map_smul]
  change ‖∑ p ∈ d.support,d p • spatialElementary p.1 p.2‖ ≤
    ‖∑ p ∈ d.support,d p • spatialElementary (φ p.1) (ψ p.2)‖
  simpa only [map_smul,spatialElementary_smul_left] using
    norm_spatialSum_le_image_any d.support (fun p => d p • p.1) Prod.snd φ ψ hφ hψ

lemma minimalMapAny_isometry (φ : A →⋆ₙₐ[ℂ] B) (ψ : C →⋆ₙₐ[ℂ] D)
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) : Isometry (minimalMapAny φ ψ) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_minimalMapAny φ ψ hφ hψ)

end

end

end WeakPureInfiniteness
end

end OAI
