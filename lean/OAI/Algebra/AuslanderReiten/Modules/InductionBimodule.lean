import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorPi
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Module.Projective

namespace OAI

noncomputable section
namespace ArExplicit

@[ext] structure InductionBimodule {k R S : Type*} [CommRing k] [Ring R] [Ring S]
    [Algebra k R] [Algebra k S] (ι : R →ₐ[k] S) where
  value : S

namespace InductionBimodule
variable {k R S : Type*} [CommRing k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (ι : R →ₐ[k] S)

def coordinates : InductionBimodule ι ≃ S where
  toFun := value
  invFun := InductionBimodule.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (InductionBimodule ι) := (coordinates ι).addCommGroup
instance : Module S (InductionBimodule ι) := (coordinates ι).addEquiv.module S
instance : Module k (InductionBimodule ι) := (coordinates ι).addEquiv.module k
instance : SMul Rᵐᵒᵖ (InductionBimodule ι) := ⟨fun r x => ⟨x.value * ι r.unop⟩⟩

@[simp] theorem value_zero : (0 : InductionBimodule ι).value = 0 := rfl
@[simp] theorem value_add (x y : InductionBimodule ι) : (x + y).value = x.value + y.value := rfl
@[simp] theorem value_smul (s : S) (x : InductionBimodule ι) : (s • x).value = s * x.value := rfl
@[simp] theorem value_scalar (a : k) (x : InductionBimodule ι) : (a • x).value = a • x.value := rfl
@[simp] theorem value_right (r : Rᵐᵒᵖ) (x : InductionBimodule ι) :
    (r • x).value = x.value * ι r.unop := rfl

instance : Module Rᵐᵒᵖ (InductionBimodule ι) where
  one_smul x := by ext; simp
  mul_smul r s x := by ext; simp [mul_assoc]
  smul_zero r := by ext; simp
  smul_add r x y := by ext; simp [add_mul]
  add_smul r s x := by ext; simp [mul_add]
  zero_smul x := by ext; simp

instance : SMulCommClass S Rᵐᵒᵖ (InductionBimodule ι) where
  smul_comm s r x := by ext; exact (mul_assoc _ _ _).symm
instance : SMulCommClass k S (InductionBimodule ι) where
  smul_comm a s x := by ext; exact (mul_smul_comm a s x.value).symm
instance : IsScalarTower k S (InductionBimodule ι) where
  smul_assoc a s x := by ext; exact smul_mul_assoc a s x.value
instance : IsScalarTower k Rᵐᵒᵖ (InductionBimodule ι) where
  smul_assoc a r x := by
    ext
    change x.value * ι (a • r.unop) = a • (x.value * ι r.unop)
    rw [map_smul, mul_smul_comm]
instance : SMulCommClass k Rᵐᵒᵖ (InductionBimodule ι) where
  smul_comm a r x := by ext; exact (smul_mul_assoc a x.value (ι r.unop)).symm

def leftEquiv : InductionBimodule ι ≃ₗ[S] S := (coordinates ι).addEquiv.linearEquiv S
def scalarEquiv : InductionBimodule ι ≃ₗ[k] S := (coordinates ι).addEquiv.linearEquiv k

instance : Module.Free S (InductionBimodule ι) := Module.Free.of_equiv (leftEquiv ι).symm
instance : Module.Projective S (InductionBimodule ι) := Module.Projective.of_free
instance : Module.Finite S (InductionBimodule ι) := Module.Finite.equiv (leftEquiv ι).symm

end InductionBimodule
end ArExplicit

end

end OAI
