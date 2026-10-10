import Mathlib
import OAI.Analysis.WeakInfiniteness.CrossUniverseTensorBound

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

universe u v w x

section

variable {A : Type u} {B : Type v} {C : Type w} {D : Type x}
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

lemma minimalElementary_mul (a a' : A) (c c' : C) :
    minimalElementary (a*a') (c*c')=minimalElementary a c*minimalElementary a' c' :=
  Subtype.ext (spatialElementary_mul a a' c c')

lemma minimalElementary_star (a : A) (c : C) :
    minimalElementary (star a) (star c)=star (minimalElementary a c) :=
  Subtype.ext (spatialElementary_star a c)

lemma minimalElementary_smul_left (t : ℂ) (a : A) (c : C) :
    minimalElementary (t • a) c=t • minimalElementary a c :=
  Subtype.ext (spatialElementary_smul_left t a c)

variable (φ : A →⋆ₙₐ[ℂ] B) (ψ : C →⋆ₙₐ[ℂ] D)

def crossTensorPair (p : A × C) : MinimalTensor A C × MinimalTensor B D :=
  (minimalElementary p.1 p.2,minimalElementary (φ p.1) (ψ p.2))

lemma crossTensorPair_mul (p q : A × C) : crossTensorPair φ ψ (p*q)=
    crossTensorPair φ ψ p*crossTensorPair φ ψ q := by
  ext <;> simp only [crossTensorPair,Prod.fst_mul,Prod.snd_mul,map_mul,minimalElementary_mul]

lemma crossTensorPair_star (p : A × C) : crossTensorPair φ ψ (star p)=star (crossTensorPair φ ψ p) := by
  ext <;> simp only [crossTensorPair,Prod.fst_star,Prod.snd_star,map_star,minimalElementary_star]

def crossTensorGraph : NonUnitalStarSubalgebra ℂ (MinimalTensor A C × MinimalTensor B D) :=
  (NonUnitalStarAlgebra.adjoin ℂ (Set.range (crossTensorPair φ ψ))).topologicalClosure

instance crossTensorGraphCStar : NonUnitalCStarAlgebra (crossTensorGraph φ ψ) := by
  letI : IsClosed (crossTensorGraph φ ψ : Set (MinimalTensor A C × MinimalTensor B D)) := isClosed_closure
  infer_instance

lemma crossTensorGraph_norm (z : crossTensorGraph φ ψ) : ‖z.val.2‖ ≤ ‖z.val.1‖ := by
  have hz := z.property
  change z.val ∈ closure (NonUnitalStarAlgebra.adjoin ℂ (Set.range (crossTensorPair φ ψ)) : Set _) at hz
  rw [closure_adjoin_eq_closure_span _
    (by rintro _ ⟨p,rfl⟩ _ ⟨q,rfl⟩; exact ⟨p*q,crossTensorPair_mul φ ψ p q⟩)
    (by rintro _ ⟨p,rfl⟩; exact ⟨star p,crossTensorPair_star φ ψ p⟩)] at hz
  apply closure_minimal (t := {z : MinimalTensor A C × MinimalTensor B D | ‖z.2‖ ≤ ‖z.1‖})
    ?_ (isClosed_le (by fun_prop) (by fun_prop)) hz
  intro z hz
  classical
  obtain ⟨d,rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hz
  change ‖(d.sum fun p t => t • crossTensorPair φ ψ p).2‖ ≤
    ‖(d.sum fun p t => t • crossTensorPair φ ψ p).1‖
  simp only [Finsupp.sum,Prod.snd_sum,Prod.fst_sum,crossTensorPair]
  change ‖(minimalTensorSubalgebra B D).subtype (∑ p ∈ d.support,d p • minimalElementary (φ p.1) (ψ p.2))‖ ≤
    ‖(minimalTensorSubalgebra A C).subtype (∑ p ∈ d.support,d p • minimalElementary p.1 p.2)‖
  simp only [map_sum,map_smul]
  change ‖∑ p ∈ d.support,d p • spatialElementary (φ p.1) (ψ p.2)‖ ≤
    ‖∑ p ∈ d.support,d p • spatialElementary p.1 p.2‖
  simpa only [map_smul,spatialElementary_smul_left] using
    norm_spatialSum_map_any d.support (fun p => d p • p.1) Prod.snd φ ψ

def crossTensorFirst : crossTensorGraph φ ψ →⋆ₙₐ[ℂ] MinimalTensor A C where
  toFun z := z.val.1
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

def crossTensorSecond : crossTensorGraph φ ψ →⋆ₙₐ[ℂ] MinimalTensor B D where
  toFun z := z.val.2
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

lemma crossTensorFirst_isometry : Isometry (crossTensorFirst φ ψ) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro z
  change ‖z.val.1‖=‖z.val‖
  rw [Prod.norm_def,max_eq_left (crossTensorGraph_norm φ ψ z)]

lemma crossTensorFirst_surjective : Function.Surjective (crossTensorFirst φ ψ) := by
  let F := (NonUnitalStarSubalgebraClass.subtype (minimalTensorSubalgebra A C)).comp (crossTensorFirst φ ψ)
  have hle : minimalTensorSubalgebra A C ≤ NonUnitalStarAlgHom.range F := by
    apply NonUnitalStarSubalgebra.topologicalClosure_minimal _ (NonUnitalStarAlgebra.adjoin_le ?_)
    · exact nonUnitalStarHom_isClosed_range F
    · rintro _ ⟨p,rfl⟩
      refine ⟨⟨crossTensorPair φ ψ p,?_⟩,rfl⟩
      exact NonUnitalStarSubalgebra.le_topologicalClosure _
        (NonUnitalStarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self p))
  intro z
  obtain ⟨y,hy⟩ := hle z.property
  exact ⟨y,Subtype.ext hy⟩

def minimalMapAny : MinimalTensor A C →⋆ₙₐ[ℂ] MinimalTensor B D :=
  (crossTensorSecond φ ψ).comp
    (StarAlgEquiv.ofBijective (crossTensorFirst φ ψ)
      ⟨(crossTensorFirst_isometry φ ψ).injective,crossTensorFirst_surjective φ ψ⟩).symm.toNonUnitalStarAlgHom

@[simp] lemma minimalMapAny_elementary (a : A) (c : C) :
    minimalMapAny φ ψ (minimalElementary a c)=minimalElementary (φ a) (ψ c) := by
  let z : crossTensorGraph φ ψ := ⟨crossTensorPair φ ψ (a,c),
    NonUnitalStarSubalgebra.le_topologicalClosure _
      (NonUnitalStarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self (a,c)))⟩
  let e := StarAlgEquiv.ofBijective (crossTensorFirst φ ψ)
    ⟨(crossTensorFirst_isometry φ ψ).injective,crossTensorFirst_surjective φ ψ⟩
  have he : e z=minimalElementary a c := rfl
  change (e.symm (minimalElementary a c)).val.2=_
  rw [← he,StarAlgEquiv.symm_apply_apply]
  rfl

end

end

end WeakPureInfiniteness
end

end OAI
