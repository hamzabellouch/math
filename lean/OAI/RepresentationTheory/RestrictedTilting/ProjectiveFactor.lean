import Mathlib

namespace OAI

namespace FiberFunctorProof
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

 
def FactorsThroughProjective {C : Type*} [Category* C] {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ P : C, Projective P ∧ ∃ a : X ⟶ P, ∃ b : P ⟶ Y, a ≫ b = f

variable {k : Type*} [Field k]
variable {C : Type*} [Category* C] [Preadditive C] [Linear k C]
variable [HasFiniteBiproducts C] {X Y : C}

lemma FactorsThroughProjective.zero : FactorsThroughProjective (0 : X ⟶ Y) := by
  refine ⟨0, (isZero_zero C).projective, 0, 0, ?_⟩
  simp

lemma FactorsThroughProjective.add {f g : X ⟶ Y}
    (hf : FactorsThroughProjective f) (hg : FactorsThroughProjective g) :
    FactorsThroughProjective (f+g) := by
  obtain ⟨P,hP,a,b,rfl⟩ := hf
  obtain ⟨Q,hQ,c,d,rfl⟩ := hg
  let : HasBinaryBiproducts C := hasBinaryBiproducts_of_finite_biproducts C
  let := hP
  let := hQ
  exact ⟨P ⊞ Q, inferInstance, biprod.lift a c, biprod.desc b d, by simp⟩

omit [HasFiniteBiproducts C] in
lemma FactorsThroughProjective.smul {f : X ⟶ Y}
    (a : k) (hf : FactorsThroughProjective f) : FactorsThroughProjective (a • f) := by
  obtain ⟨P,hP,b,c,rfl⟩ := hf
  exact ⟨P,hP,a • b,c, by simp⟩

 

def projectiveFactorSubmodule (X Y : C) : Submodule k (X ⟶ Y) where
  carrier := {f | FactorsThroughProjective f}
  zero_mem' := FactorsThroughProjective.zero
  add_mem' := FactorsThroughProjective.add
  smul_mem' := fun a _ h => FactorsThroughProjective.smul a h
end FiberFunctorProof

end OAI
