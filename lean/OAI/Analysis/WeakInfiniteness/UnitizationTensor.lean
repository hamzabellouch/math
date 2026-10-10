import Mathlib
import OAI.Analysis.WeakInfiniteness.FaithfulRepresentation
import OAI.Analysis.WeakInfiniteness.TensorCut
import OAI.Analysis.WeakInfiniteness.TensorInjectivity

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

universe u

noncomputable section

open scoped TensorProduct ComplexOrder ENNReal

open UniformSpace

variable {A C D : Type u} [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

lemma spatialElementary_ne_zero {a : A} {c : C} (ha : a≠0) (hc : c≠0) :
    spatialElementary a c≠0 := by
  obtain ⟨H,π,hπ⟩ := exists_faithful_representation A
  obtain ⟨K,ρ,hρ⟩ := exists_faithful_representation C
  have hπa : π a≠0 := by intro h; apply ha; apply hπ; simpa using h
  have hρc : ρ c≠0 := by intro h; apply hc; apply hρ; simpa using h
  obtain ⟨ξ,hξ⟩ : ∃ ξ : H, π a ξ≠0 := by
    by_contra h
    apply hπa
    ext ξ
    simpa using not_exists.mp h ξ
  obtain ⟨η,hη⟩ : ∃ η : K, ρ c η≠0 := by
    by_contra h
    apply hρc
    ext η
    simpa using not_exists.mp h η
  let σ : SpatialRepresentation A C := {left := H, right := K, leftRep := π, rightRep := ρ}
  intro h
  have hh := congrArg (fun z : SpatialAmbient A C => z σ ((ξ ⊗ₜ[ℂ] η : H ⊗[ℂ] K) : Completion _)) h
  change ((TensorProduct.mapL (π a) (ρ c)).completion _)=0 at hh
  rw [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul] at hh
  have hn := congrArg norm hh
  rw [Completion.norm_coe, TensorProduct.norm_tmul, norm_zero] at hn
  exact (ne_of_gt (mul_pos (norm_pos_iff.mpr hξ) (norm_pos_iff.mpr hη))) hn

lemma rightElementaryHom_injective {E : Type u} [CStarAlgebra E] [Nontrivial E] :
    Function.Injective (rightElementaryHom (A := E) (C := C)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro c hc
  by_contra h
  exact spatialElementary_ne_zero (one_ne_zero : (1 : E)≠0) h (congrArg Subtype.val hc)

lemma minimalTensor_closed_submodule (S : Submodule ℂ (MinimalTensor A C))
    (hS : IsClosed (S : Set (MinimalTensor A C)))
    (he : ∀ a c, minimalElementary a c∈S) (x : MinimalTensor A C) : x∈S := by
  let j : MinimalTensor A C →ₗ[ℂ] SpatialAmbient A C :=
    { toFun := Subtype.val, map_add' _ _ := rfl, map_smul' _ _ := rfl }
  let T := S.map j
  have hTc : IsClosed (T : Set (SpatialAmbient A C)) :=
    isClosed_closure.isClosedMap_subtype_val _ hS
  have hs : Submodule.span ℂ (Set.range fun p : A×C => spatialElementary p.1 p.2) ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,c⟩,rfl⟩
    exact ⟨minimalElementary a c,he a c,rfl⟩
  have hx := x.property
  change x.val ∈ (minimalTensorSubalgebra A C : Set (SpatialAmbient A C)) at hx
  rw [minimalTensor_eq_closure_span] at hx
  obtain ⟨y,hy,hyx⟩ := (closure_minimal hs hTc) hx
  exact (Subtype.ext hyx : y=x) ▸ hy

lemma minimalMapLeft_right_commute {B : Type u} [NonUnitalCStarAlgebra B]
    (φ : A →⋆ₙₐ[ℂ] B) (q : C →⋆ₙₐ[ℂ] D) (z : MinimalTensor A C) :
    minimalMapRight q (minimalMapLeft φ z)=minimalMapLeft φ (minimalMapRight q z) := rfl

lemma minimalMapRight_eq_zero_iff (q : C →⋆ₙₐ[ℂ] D) (z : MinimalTensor A C) :
    minimalMapRight q z=0 ↔ ∀ π : SpatialRepresentation A D, z.val (π.precompRight q)=0 := by
  constructor
  · intro h π
    exact congrArg (fun z : MinimalTensor A D => z.val π) h
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    exact funext h

end

end WeakPureInfiniteness
end

end OAI
