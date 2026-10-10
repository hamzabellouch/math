import Mathlib
import OAI.Analysis.WeakInfiniteness.FaithfulRepresentation
import OAI.Analysis.WeakInfiniteness.UniformModels

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

open UniformSpace

universe u v w x

section

variable {A : Type u} {C : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra C]

variable {H : Type w} {K : Type x} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma norm_tensorSum_le_spatial_any {ι : Type*} (s : Finset ι) (a : ι → A) (c : ι → C)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ρ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    ‖∑ i ∈ s, TensorProduct.mapL (π (a i)) (ρ (c i))‖ ≤
      ‖∑ i ∈ s, spatialElementary (a i) (c i)‖ := by
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  let := CStarAlgebra.spectralOrder C
  let := CStarAlgebra.spectralOrderedRing C
  obtain ⟨H₀,π₀,hπ₀⟩ := exists_faithful_representation A
  obtain ⟨K₀,ρ₀,hρ₀⟩ := exists_faithful_representation C
  let H' : ComplexHilbert.{max u v} := ⟨ULift.{v} H₀⟩
  let K' : ComplexHilbert.{max u v} := ⟨ULift.{u} K₀⟩
  let e : H₀ ≃ₗᵢ[ℂ] H' := (LinearIsometryEquiv.ulift ℂ H₀).symm
  let f : K₀ ≃ₗᵢ[ℂ] K' := (LinearIsometryEquiv.ulift ℂ K₀).symm
  let π' := e.conjStarAlgEquiv.toNonUnitalStarAlgHom.comp π₀
  let ρ' := f.conjStarAlgEquiv.toNonUnitalStarAlgHom.comp ρ₀
  have hπ' : Function.Injective π' := e.conjStarAlgEquiv.injective.comp hπ₀
  have hρ' : Function.Injective ρ' := f.conjStarAlgEquiv.injective.comp hρ₀
  let σ : SpatialRepresentation A C := {left := H',right := K',leftRep := π',rightRep := ρ'}
  calc
    _ ≤ ‖∑ i ∈ s,TensorProduct.mapL (π (a i)) (ρ' (c i))‖ :=
      tensor_norm_le_faithful_finset s (fun i => π (a i)) c ρ' ρ hρ'
    _ = ‖∑ i ∈ s,TensorProduct.mapL (ρ' (c i)) (π (a i))‖ := norm_tensorSum_flip s _ _
    _ ≤ ‖∑ i ∈ s,TensorProduct.mapL (ρ' (c i)) (π' (a i))‖ :=
      tensor_norm_le_faithful_finset s (fun i => ρ' (c i)) a π' π hπ'
    _ = ‖∑ i ∈ s,TensorProduct.mapL (π' (a i)) (ρ' (c i))‖ := norm_tensorSum_flip s _ _
    _ = ‖(∑ i ∈ s, spatialElementary (a i) (c i)) σ‖ := by rw [spatialSum_apply,norm_completion]
    _ ≤ _ := lp.norm_apply_le_norm ENNReal.top_ne_zero _ σ

end

lemma norm_spatialSum_map_any {A : Type u} {B : Type v} {C : Type w} {D : Type x}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]
    {ι : Type*} (s : Finset ι) (a : ι → A) (c : ι → C)
    (φ : A →⋆ₙₐ[ℂ] B) (ψ : C →⋆ₙₐ[ℂ] D) :
    ‖∑ i ∈ s,spatialElementary (φ (a i)) (ψ (c i))‖ ≤
      ‖∑ i ∈ s,spatialElementary (a i) (c i)‖ := by
  apply lp.norm_le_of_forall_le (norm_nonneg _)
  intro π
  rw [spatialSum_apply,norm_completion]
  exact norm_tensorSum_le_spatial_any s a c (π.leftRep.comp φ) (π.rightRep.comp ψ)

end

end WeakPureInfiniteness
end

end OAI
