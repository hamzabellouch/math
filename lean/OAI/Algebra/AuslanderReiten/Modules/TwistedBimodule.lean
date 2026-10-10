import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.RingTheory.Finiteness.Basic

namespace OAI

namespace ArExplicit

@[ext] structure TwistedBimodule (k R : Type*) [CommRing k] [Ring R] [Algebra k R]
    (σ : R ≃ₐ[k] R) where
  value : R

namespace TwistedBimodule

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R] (σ : R ≃ₐ[k] R)

def coordinates : TwistedBimodule k R σ ≃ R where
  toFun := value
  invFun := TwistedBimodule.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (TwistedBimodule k R σ) := (coordinates σ).addCommGroup
instance : Module R (TwistedBimodule k R σ) := (coordinates σ).addEquiv.module R
instance : Module k (TwistedBimodule k R σ) := (coordinates σ).addEquiv.module k

@[simp] theorem value_zero : (0 : TwistedBimodule k R σ).value = 0 := rfl
@[simp] theorem value_add (x y : TwistedBimodule k R σ) :
    (x + y).value = x.value + y.value := rfl
@[simp] theorem value_left_smul (r : R) (x : TwistedBimodule k R σ) :
    (r • x).value = r * x.value := rfl
@[simp] theorem value_scalar_smul (c : k) (x : TwistedBimodule k R σ) :
    (c • x).value = c • x.value := rfl

instance : SMul Rᵐᵒᵖ (TwistedBimodule k R σ) :=
  ⟨fun r x => ⟨x.value * σ r.unop⟩⟩

@[simp] theorem value_right_smul (r : Rᵐᵒᵖ) (x : TwistedBimodule k R σ) :
    (r • x).value = x.value * σ r.unop := rfl

instance : Module Rᵐᵒᵖ (TwistedBimodule k R σ) where
  one_smul x := by ext; simp
  mul_smul r s x := by ext; simp [mul_assoc]
  smul_zero r := by ext; simp
  smul_add r x y := by ext; simp [add_mul]
  add_smul r s x := by ext; simp [mul_add]
  zero_smul x := by ext; simp

instance : SMulCommClass R Rᵐᵒᵖ (TwistedBimodule k R σ) where
  smul_comm r s x := by ext; exact (mul_assoc _ _ _).symm

instance : IsScalarTower k R (TwistedBimodule k R σ) where
  smul_assoc c r x := by ext; exact smul_mul_assoc c r x.value

instance : SMulCommClass k R (TwistedBimodule k R σ) where
  smul_comm c r x := by ext; exact (mul_smul_comm c r x.value).symm

instance : IsScalarTower k Rᵐᵒᵖ (TwistedBimodule k R σ) where
  smul_assoc c r x := by
    ext
    change x.value * σ (c • r.unop) = c • (x.value * σ r.unop)
    rw [map_smul, mul_smul_comm]

instance : SMulCommClass k Rᵐᵒᵖ (TwistedBimodule k R σ) where
  smul_comm c r x := by ext; exact (smul_mul_assoc c x.value (σ r.unop)).symm

def leftLinearEquiv : TwistedBimodule k R σ ≃ₗ[R] R := (coordinates σ).addEquiv.linearEquiv R

def rightLinearEquiv : TwistedBimodule k R σ ≃ₗ[Rᵐᵒᵖ] Rᵐᵒᵖ where
  toFun x := MulOpposite.op (σ.symm x.value)
  invFun x := ⟨σ x.unop⟩
  left_inv x := by ext; exact σ.apply_symm_apply x.value
  right_inv x := by simp
  map_add' x y := by simp
  map_smul' r x := by
    apply MulOpposite.unop_injective
    change σ.symm (x.value * σ r.unop) = σ.symm x.value * r.unop
    simp

def scalarLinearEquiv : TwistedBimodule k R σ ≃ₗ[k] R := (coordinates σ).addEquiv.linearEquiv k

instance : Module.Projective R (TwistedBimodule k R σ) :=
  Module.Projective.of_equiv (leftLinearEquiv σ).symm

instance : Module.Projective Rᵐᵒᵖ (TwistedBimodule k R σ) :=
  Module.Projective.of_equiv (rightLinearEquiv σ).symm

instance : Module.Finite R (TwistedBimodule k R σ) :=
  Module.Finite.equiv (leftLinearEquiv σ).symm

instance : Module.Finite Rᵐᵒᵖ (TwistedBimodule k R σ) :=
  Module.Finite.equiv (rightLinearEquiv σ).symm

instance [Module.Finite k R] : Module.Finite k (TwistedBimodule k R σ) :=
  Module.Finite.equiv (scalarLinearEquiv σ).symm

end TwistedBimodule
end ArExplicit

end OAI
