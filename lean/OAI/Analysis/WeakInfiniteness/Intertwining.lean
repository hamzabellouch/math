import Mathlib

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

open scoped Topology CStarAlgebra

section

variable {B : Type*} [CStarAlgebra B]

local instance : Algebra ℝ (B × B) := Algebra.complexToReal

def intertwiningAlgebra (D : B) : StarSubalgebra ℂ (B × B) where
  carrier := {z | z.1*D=D*z.2 ∧ star D*z.1=z.2*star D}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    rintro ⟨x₁,x₂⟩ ⟨y₁,y₂⟩ ⟨hx,hx'⟩ ⟨hy,hy'⟩
    constructor <;> dsimp at *
    · simp only [add_mul,mul_add,hx,hy]
    · simp only [add_mul,mul_add,hx',hy']
  mul_mem' := by
    rintro ⟨x₁,x₂⟩ ⟨y₁,y₂⟩ ⟨hx,hx'⟩ ⟨hy,hy'⟩
    constructor <;> dsimp at *
    · rw [mul_assoc,hy,← mul_assoc,hx,mul_assoc]
    · rw [← mul_assoc,hx',mul_assoc,hy',← mul_assoc]
  algebraMap_mem' := by intro c; simp only [Set.mem_ofPred_eq,Prod.algebraMap_apply]; constructor <;> simp [Algebra.commutes]
  star_mem' := by
    rintro ⟨x₁,x₂⟩ ⟨hx,hx'⟩
    constructor <;> dsimp at *
    · simpa only [star_mul,star_star] using congrArg star hx'
    · simpa only [star_mul,star_star] using congrArg star hx

instance intertwiningAlgebra_isClosed (D : B) : IsClosed (intertwiningAlgebra D : Set (B × B)) := by
  change IsClosed {z : B × B | z.1*D=D*z.2 ∧ star D*z.1=z.2*star D}
  exact (isClosed_eq (by fun_prop) (by fun_prop)).inter (isClosed_eq (by fun_prop) (by fun_prop))

lemma cfc_star_mul_intertwine (D : B) (f : ℝ → ℝ) (hf : Continuous f) :
    cfc f (D*star D)*D=D*cfc f (star D*D) := by
  have hm : (D*star D,star D*D) ∈ intertwiningAlgebra D := by
    constructor <;> simp only [mul_assoc]
  have h := cfc_mem f hm
  have hprod : IsSelfAdjoint (D*star D,star D*D) := by
    change star (D*star D,star D*D)=(D*star D,star D*D)
    apply Prod.ext
    · exact IsSelfAdjoint.mul_star_self D
    · exact IsSelfAdjoint.star_mul_self D
  have hfst := (StarAlgHom.fst ℂ B B).map_cfc f (D*star D,star D*D)
    hf.continuousOn continuous_fst hprod (IsSelfAdjoint.mul_star_self D)
  have hsnd := (StarAlgHom.snd ℂ B B).map_cfc f (D*star D,star D*D)
    hf.continuousOn continuous_snd hprod (IsSelfAdjoint.star_mul_self D)
  change (cfc f (D*star D,star D*D)).1=cfc f (D*star D) at hfst
  change (cfc f (D*star D,star D*D)).2=cfc f (star D*D) at hsnd
  change (cfc f (D*star D,star D*D)).1*D=D*(cfc f (D*star D,star D*D)).2 ∧ _ at h
  rw [hfst,hsnd] at h
  exact h.1

end

end

end WeakPureInfiniteness
end

end OAI
