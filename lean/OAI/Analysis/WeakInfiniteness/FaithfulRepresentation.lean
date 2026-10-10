import Mathlib
import OAI.Analysis.WeakInfiniteness.States
import OAI.Analysis.WeakInfiniteness.TensorFoundations

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

open scoped ENNReal ComplexOrder InnerProductSpace

section DirectSum

variable {A : Type*} [NonUnitalCStarAlgebra A]

variable {ι : Type*} {H : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]

def sumRepresentation (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) :
    A →⋆ₙₐ[ℂ] (lp H 2 →L[ℂ] lp H 2) where
  toFun a := lp.mapCLM 2 (fun i => π i a) (norm_nonneg a)
    (fun i => NonUnitalStarAlgHom.norm_apply_le (π i) a)
  map_zero' := by ext x i; simp [lp.mapCLM]
  map_add' a b := by
    ext x i
    change π i (a+b) (x i)=π i a (x i)+π i b (x i)
    rw [map_add, add_apply]
  map_smul' r a := by ext x i; simp [lp.mapCLM]
  map_mul' a b := by ext x i; simp [lp.mapCLM]
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
      lp.inner_eq_tsum, lp.inner_eq_tsum]
    apply tsum_congr
    intro i
    change inner ℂ (y i) (π i (star a) (x i))=inner ℂ (π i a (y i)) (x i)
    rw [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]

@[simp] lemma sumRepresentation_apply (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i))
    (a : A) (x : lp H 2) (i : ι) : sumRepresentation π a x i=π i a (x i) := rfl

lemma sumRepresentation_injective (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i))
    (hπ : ∀ a : A, (∀ i, π i a=0) → a=0) : Function.Injective (sumRepresentation π) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  apply hπ a
  intro i
  ext ξ
  have h := congrArg (fun T : lp H 2 →L[ℂ] lp H 2 => T (lp.single 2 i ξ) i) ha
  simpa using h

end DirectSum

universe hilbertUniverse

section GNSFaithful

variable (A : Type hilbertUniverse) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def universalGNSHilbert : ComplexHilbert.{hilbertUniverse} where
  Carrier := lp (fun f : A →ₚ[ℂ] ℂ => f.GNS) 2

def universalGNSRepresentation : A →⋆ₙₐ[ℂ]
    (universalGNSHilbert A →L[ℂ] universalGNSHilbert A) :=
  sumRepresentation (fun f : A →ₚ[ℂ] ℂ => f.gnsNonUnitalStarAlgHom)

lemma universalGNSRepresentation_injective : Function.Injective (universalGNSRepresentation A) := by
  apply sumRepresentation_injective
  intro a ha
  by_cases hA : Subsingleton A
  · exact Subsingleton.elim _ _
  · have : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
    obtain ⟨f,_,hf⟩ := exists_norming_gns a
    apply norm_eq_zero.mp
    rw [← hf]
    change ‖f.gnsNonUnitalStarAlgHom a‖=0
    rw [ha f, norm_zero]

end GNSFaithful

theorem exists_faithful_representation (A : Type hilbertUniverse) [NonUnitalCStarAlgebra A] :
    ∃ (H : ComplexHilbert.{hilbertUniverse}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)), Function.Injective π := by
  let U := Unitization ℂ A
  let := CStarAlgebra.spectralOrder U
  let := CStarAlgebra.spectralOrderedRing U
  refine ⟨universalGNSHilbert U,
    (universalGNSRepresentation U).comp (Unitization.inrNonUnitalStarAlgHom ℂ A), ?_⟩
  exact (universalGNSRepresentation_injective U).comp Unitization.inr_injective

end

end WeakPureInfiniteness
end

end OAI
