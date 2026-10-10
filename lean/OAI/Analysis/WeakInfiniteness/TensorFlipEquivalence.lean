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

open scoped TensorProduct ENNReal

open UniformSpace Topology

universe u v

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

lemma norm_spatialSum_flip {ι : Type*} (s : Finset ι) (a : ι → A) (b : ι → B) :
    ‖∑ i ∈ s,spatialElementary (a i) (b i)‖ =
      ‖∑ i ∈ s,spatialElementary (b i) (a i)‖ := by
  apply le_antisymm
  · apply lp.norm_le_of_forall_le (norm_nonneg _)
    intro π
    rw [spatialSum_apply,norm_completion,norm_tensorSum_flip]
    exact norm_tensorSum_le_spatial_any s b a π.rightRep π.leftRep
  · apply lp.norm_le_of_forall_le (norm_nonneg _)
    intro π
    rw [spatialSum_apply,norm_completion,norm_tensorSum_flip]
    exact norm_tensorSum_le_spatial_any s a b π.rightRep π.leftRep

def tensorFlipPair (p : A × B) : MinimalTensor A B × MinimalTensor B A :=
  (minimalElementary p.1 p.2,minimalElementary p.2 p.1)

lemma tensorFlipPair_mul (p q : A × B) : tensorFlipPair (p*q)=
    tensorFlipPair p*tensorFlipPair q := by
  ext <;> simp only [tensorFlipPair,Prod.fst_mul,Prod.snd_mul,minimalElementary_mul]

lemma tensorFlipPair_star (p : A × B) : tensorFlipPair (star p)=star (tensorFlipPair p) := by
  ext <;> simp only [tensorFlipPair,Prod.fst_star,Prod.snd_star,minimalElementary_star]

variable (A B) in

def tensorFlipGraph : NonUnitalStarSubalgebra ℂ (MinimalTensor A B × MinimalTensor B A) :=
  (NonUnitalStarAlgebra.adjoin ℂ (Set.range (tensorFlipPair (A := A) (B := B)))).topologicalClosure

instance tensorFlipGraphCStar : NonUnitalCStarAlgebra (tensorFlipGraph A B) := by
  letI : IsClosed (tensorFlipGraph A B : Set (MinimalTensor A B × MinimalTensor B A)) := isClosed_closure
  infer_instance

lemma tensorFlipGraph_norm (z : tensorFlipGraph A B) : ‖z.val.2‖=‖z.val.1‖ := by
  have hz := z.property
  change z.val ∈ closure (NonUnitalStarAlgebra.adjoin ℂ (Set.range (tensorFlipPair (A := A) (B := B))) : Set _) at hz
  rw [closure_adjoin_eq_closure_span _
    (by rintro _ ⟨p,rfl⟩ _ ⟨q,rfl⟩; exact ⟨p*q,tensorFlipPair_mul p q⟩)
    (by rintro _ ⟨p,rfl⟩; exact ⟨star p,tensorFlipPair_star p⟩)] at hz
  apply closure_minimal (t := {z : MinimalTensor A B × MinimalTensor B A | ‖z.2‖=‖z.1‖})
    ?_ (isClosed_eq (by fun_prop) (by fun_prop)) hz
  intro z hz
  classical
  obtain ⟨d,rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hz
  change ‖(d.sum fun p t => t • tensorFlipPair p).2‖ =
    ‖(d.sum fun p t => t • tensorFlipPair p).1‖
  simp only [Finsupp.sum,Prod.snd_sum,Prod.fst_sum,tensorFlipPair]
  change ‖(minimalTensorSubalgebra B A).subtype (∑ p ∈ d.support,d p • minimalElementary p.2 p.1)‖ =
    ‖(minimalTensorSubalgebra A B).subtype (∑ p ∈ d.support,d p • minimalElementary p.1 p.2)‖
  simp only [map_sum,map_smul]
  change ‖∑ p ∈ d.support,d p • spatialElementary p.2 p.1‖ =
    ‖∑ p ∈ d.support,d p • spatialElementary p.1 p.2‖
  simpa only [spatialElementary_smul_left,spatialElementary_smul_right] using
    norm_spatialSum_flip d.support (fun p => d p • p.2) Prod.fst

def tensorFlipFirst : tensorFlipGraph A B →⋆ₙₐ[ℂ] MinimalTensor A B where
  toFun z := z.val.1
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

def tensorFlipSecond : tensorFlipGraph A B →⋆ₙₐ[ℂ] MinimalTensor B A where
  toFun z := z.val.2
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

lemma tensorFlipFirst_isometry : Isometry (tensorFlipFirst (A := A) (B := B)) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro z
  change ‖z.val.1‖ = ‖z.val‖
  rw [Prod.norm_def,tensorFlipGraph_norm z,max_self]

lemma tensorFlipFirst_surjective : Function.Surjective (tensorFlipFirst (A := A) (B := B)) := by
  let F := (NonUnitalStarSubalgebraClass.subtype (minimalTensorSubalgebra A B)).comp tensorFlipFirst
  have hle : minimalTensorSubalgebra A B ≤ NonUnitalStarAlgHom.range F := by
    apply NonUnitalStarSubalgebra.topologicalClosure_minimal _ (NonUnitalStarAlgebra.adjoin_le ?_)
    · exact nonUnitalStarHom_isClosed_range F
    · rintro _ ⟨p,rfl⟩
      refine ⟨⟨tensorFlipPair p,?_⟩,rfl⟩
      exact NonUnitalStarSubalgebra.le_topologicalClosure _
        (NonUnitalStarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self p))
  intro z
  obtain ⟨y,hy⟩ := hle z.property
  exact ⟨y,Subtype.ext hy⟩

variable (A B) in

def minimalFlipHom : MinimalTensor A B →⋆ₙₐ[ℂ] MinimalTensor B A :=
  (tensorFlipSecond (A := A) (B := B)).comp
    (StarAlgEquiv.ofBijective (tensorFlipFirst (A := A) (B := B))
      ⟨(tensorFlipFirst_isometry (A := A) (B := B)).injective,tensorFlipFirst_surjective⟩).symm.toNonUnitalStarAlgHom

@[simp] lemma minimalFlipHom_elementary (a : A) (b : B) :
    minimalFlipHom A B (minimalElementary a b)=minimalElementary b a := by
  let z : tensorFlipGraph A B := ⟨tensorFlipPair (a,b),
    NonUnitalStarSubalgebra.le_topologicalClosure _
      (NonUnitalStarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self (a,b)))⟩
  let e := StarAlgEquiv.ofBijective (tensorFlipFirst (A := A) (B := B))
    ⟨(tensorFlipFirst_isometry (A := A) (B := B)).injective,tensorFlipFirst_surjective⟩
  have he : e z=minimalElementary a b := rfl
  change (e.symm (minimalElementary a b)).val.2=_
  rw [← he,StarAlgEquiv.symm_apply_apply]
  rfl

lemma minimalFlipHom_involutive (z : MinimalTensor A B) :
    minimalFlipHom B A (minimalFlipHom A B z)=z := by
  have h : (minimalFlipHom B A).comp (minimalFlipHom A B)=
      NonUnitalStarAlgHom.id ℂ (MinimalTensor A B) := by
    apply minimalTensor_hom_ext
    intro a b
    simp
  exact DFunLike.congr_fun h z

variable (A B) in

def minimalFlip : MinimalTensor A B ≃⋆ₐ[ℂ] MinimalTensor B A :=
  StarAlgEquiv.ofBijective (minimalFlipHom A B)
    ⟨Function.HasLeftInverse.injective ⟨minimalFlipHom B A,minimalFlipHom_involutive⟩,
      fun z => ⟨minimalFlipHom B A z,minimalFlipHom_involutive z⟩⟩

@[simp] lemma minimalFlip_elementary (a : A) (b : B) :
    minimalFlip A B (minimalElementary a b)=minimalElementary b a :=
  minimalFlipHom_elementary a b

end

end WeakPureInfiniteness
end

end OAI
