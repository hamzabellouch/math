import OAI.Algebra.Finitistic.Dimension.PDBarQuotient
import Mathlib.Algebra.Module.TransferInstance

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.PDBarQuotient
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D)
variable (V : Type u) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]

/-- The actual exterior D-action transferred through the proved quotient equivalence. -/
instance leftModule : Module D (BalancedTensor.Tensor k A (RightBase f) V) :=
  (equiv f V).toAddEquiv.module D

instance leftTower : IsScalarTower k D (BalancedTensor.Tensor k A (RightBase f) V) :=
  (equiv f V).isScalarTower (A := D)

def linearEquiv : BalancedTensor.Tensor k A (RightBase f) V ≃ₗ[D]
    DerivedBar.Balanced.tensor f V := (equiv f V).toAddEquiv.linearEquiv D

omit [IsScalarTower k A V] in
/-- The transferred action is the original left regular multiplication. -/
@[simp] theorem smul_mk (d b : D) (v : V) :
    d • BalancedTensor.mk k A (RightBase f) V b v =
      BalancedTensor.mk k A (RightBase f) V (d*b) v := by
  apply (equiv f V).injective
  exact ((linearEquiv f V).map_smul d _).trans (left_action f d b v).symm

omit [IsScalarTower k A V] in
/-- Compatibility with every exterior scalar, on arbitrary balanced tensors. -/
theorem equiv_smul (d : D) (z : BalancedTensor.Tensor k A (RightBase f) V) :
    equiv f V (d • z) = d • equiv f V z := (linearEquiv f V).map_smul d z

variable {V} {W : Type u} [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
def map (h : V →ₗ[A] W) : BalancedTensor.Tensor k A (RightBase f) V →ₗ[D]
    BalancedTensor.Tensor k A (RightBase f) W :=
  (linearEquiv f W).symm.toLinearMap.comp
    ((DerivedBar.Balanced.map f V W h).comp (linearEquiv f V).toLinearMap)

theorem map_eq (h : V →ₗ[A] W) :
    (map f h).restrictScalars k = PDTensor.mapRight (k := k) (RightBase f) h := by
  apply BalancedTensor.ext
  intro d v
  rfl
end LittleFinitistic.PDBarQuotient

end

end OAI
