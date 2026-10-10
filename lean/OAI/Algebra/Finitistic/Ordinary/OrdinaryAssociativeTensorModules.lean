import OAI.Algebra.Finitistic.Ordinary.OrdinaryBalancedActions

namespace OAI
noncomputable section
namespace LittleFinitistic
universe u
/-- A tensor retaining the right action of the middle bimodule. -/
def RightTensor (k A : Type u) (_ : Type u) (M N : Type u) [Field k] [Ring A] [Algebra k A]
    [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
    [AddCommGroup N] [Module k N] [Module A N] := BalancedTensor.Tensor k A M N

/-- A tensor retaining the left action of the middle bimodule. -/
def LeftTensor (k B : Type u) (_ : Type u) (N Z : Type u) [Field k] [Ring B] [Algebra k B]
    [AddCommGroup N] [Module k N] [Module Bᵐᵒᵖ N]
    [AddCommGroup Z] [Module k Z] [Module B Z] := BalancedTensor.Tensor k B N Z

variable (k A B M N Z : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
variable [AddCommGroup N] [Module k N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
variable [AddCommGroup Z] [Module k Z] [Module B Z] [IsScalarTower k B Z]

namespace RightTensor
instance : AddCommGroup (RightTensor k A B M N) := inferInstanceAs (AddCommGroup (BalancedTensor.Tensor k A M N))
instance : Module k (RightTensor k A B M N) := inferInstanceAs (Module k (BalancedTensor.Tensor k A M N))

local instance : SMulCommClass Bᵐᵒᵖ A N := ⟨fun b a n => (smul_comm a b n).symm⟩

def action : Bᵐᵒᵖ →ₐ[k] Module.End k (RightTensor k A B M N) :=
  BalancedTensor.rightAction
instance : Module Bᵐᵒᵖ (RightTensor k A B M N) := Module.compHom _ (action k A B M N).toRingHom
instance : IsScalarTower k Bᵐᵒᵖ (RightTensor k A B M N) where
  smul_assoc r b z := by
    change action k A B M N (r • b) z = r • action k A B M N b z
    rw [map_smul]
    rfl

def mk : M →ₗ[k] N →ₗ[k] RightTensor k A B M N := BalancedTensor.mk k A M N

omit [IsScalarTower k Aᵐᵒᵖ M] in
@[simp] theorem smul_mk (b : Bᵐᵒᵖ) (m : M) (n : N) :
    b • mk k A B M N m n = mk k A B M N m (b • n) := rfl
end RightTensor

namespace LeftTensor
instance : AddCommGroup (LeftTensor k B A N Z) := inferInstanceAs (AddCommGroup (BalancedTensor.Tensor k B N Z))
instance : Module k (LeftTensor k B A N Z) := inferInstanceAs (Module k (BalancedTensor.Tensor k B N Z))

def action : A →ₐ[k] Module.End k (LeftTensor k B A N Z) := BalancedTensor.leftAction
instance : Module A (LeftTensor k B A N Z) := Module.compHom _ (action k A B N Z).toRingHom
instance : IsScalarTower k A (LeftTensor k B A N Z) where
  smul_assoc r a z := by
    change action k A B N Z (r • a) z = r • action k A B N Z a z
    rw [map_smul]
    rfl

def mk : N →ₗ[k] Z →ₗ[k] LeftTensor k B A N Z := BalancedTensor.mk k B N Z

omit [IsScalarTower k B Z] in
@[simp] theorem smul_mk (a : A) (n : N) (z : Z) :
    a • mk k A B N Z n z = mk k A B N Z (a • n) z := rfl
end LeftTensor
end LittleFinitistic

end

end OAI
