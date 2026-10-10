import Mathlib
import OAI.Computability.MinUncut.Estimates.F2

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner
abbrev Triple := Fin 3 → F₂

structure Equation (Name : Type*) where
  names : Fin 3 → Name
  rhs : F₂
  deriving DecidableEq

variable {Name : Type*}

def parity : Triple →ₗ[F₂] F₂ where
  toFun a := a 0+a 1+a 2
  map_add' a b := by simp only [Pi.add_apply]; ring
  map_smul' c a := by simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring

@[simp] lemma parity_apply (a : Triple) : parity a = a 0+a 1+a 2 := rfl

def Valid (E : Equation Name) (a : Triple) : Prop :=
  parity a = E.rhs ∧ ∀ p p', E.names p=E.names p' → a p=a p'

def alphabet (E : Equation Name) : AffineSubspace F₂ Triple where
  carrier := {a | Valid E a}
  smul_vsub_vadd_mem' c a b d ha hb hd := by
    change parity (c • (a-b)+d)=E.rhs ∧ _
    constructor
    · rw [map_add,map_smul,map_sub,ha.1,hb.1,hd.1,sub_self,smul_zero,zero_add]
    · intro p p' he
      change c*(a p-b p)+d p=c*(a p'-b p')+d p'
      rw [ha.2 p p' he,hb.2 p p' he,hd.2 p p' he]

@[simp] lemma mem_alphabet (E : Equation Name) (a : Triple) :
    a ∈ alphabet E ↔ Valid E a := Iff.rfl

def origin (E : Equation Name) : alphabet E :=
  ⟨fun _ => E.rhs, ⟨by simp only [parity_apply,CharTwo.add_self_eq_zero,zero_add],
    fun _ _ _ => rfl⟩⟩

instance alphabetNonempty (E : Equation Name) : Nonempty (alphabet E) := ⟨origin E⟩
instance alphabetFintype (E : Equation Name) : Fintype (alphabet E) := Fintype.ofFinite _
instance directionFintype (E : Equation Name) : Fintype (alphabet E).direction := Fintype.ofFinite _

lemma direction_parity (E : Equation Name) (v : (alphabet E).direction) :
    parity (v : Triple) = 0 := by
  obtain ⟨a,ha,b,hb,he⟩ :=
    ((alphabet E).mem_direction_iff_eq_vsub ⟨origin E,(origin E).property⟩ v.val).mp v.property
  rw [he]
  change parity (a-b)=0
  rw [map_sub,ha.1,hb.1,sub_self]

def firstTwo (E : Equation Name) : (alphabet E).direction →ₗ[F₂] (Fin 2 → F₂) :=
  LinearMap.pi (fun i => (LinearMap.proj i.castSucc).comp (alphabet E).direction.subtype)

lemma firstTwo_injective (E : Equation Name) : Function.Injective (firstTwo E) := by
  intro v w hvw
  have h0 : v.val 0=w.val 0 := congrFun hvw 0
  have h1 : v.val 1=w.val 1 := congrFun hvw 1
  apply Subtype.ext
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · have hv := direction_parity E v
    have hw := direction_parity E w
    simp only [parity_apply,h0,h1] at hv hw
    exact add_left_cancel (hv.trans hw.symm)

lemma alphabet_dimension_le (E : Equation Name) :
    Module.finrank F₂ (alphabet E).direction ≤ 2 := by
  have h := (firstTwo E).finrank_le_finrank_of_injective (firstTwo_injective E)
  simpa only [Module.finrank_fin_fun] using h

def coordinates (E : Equation Name) :
    (Fin (Module.finrank F₂ (alphabet E).direction) → F₂) ≃ₗ[F₂] (alphabet E).direction :=
  (Module.finBasis F₂ (alphabet E).direction).equivFun.symm

def directionEmbedding (E : Equation Name) :
    (Fin (Module.finrank F₂ (alphabet E).direction) → F₂) →ₗ[F₂] Triple :=
  (alphabet E).direction.subtype.comp (coordinates E).toLinearMap

lemma directionEmbedding_injective (E : Equation Name) :
    Function.Injective (directionEmbedding E) :=
  Subtype.val_injective.comp (coordinates E).injective

def alphabetCoordinates (E : Equation Name) :
    (Fin (Module.finrank F₂ (alphabet E).direction) → F₂) ≃ᵃ[F₂] alphabet E :=
  (coordinates E).toAffineEquiv.trans (AffineEquiv.vaddConst F₂ (origin E))

@[simp] lemma alphabetCoordinates_val (E : Equation Name)
    (v : Fin (Module.finrank F₂ (alphabet E).direction) → F₂) :
    ((alphabetCoordinates E v : alphabet E) : Triple) =
      directionEmbedding E v + (origin E : Triple) := rfl

end MinUncut.Outer

end
end

end OAI
