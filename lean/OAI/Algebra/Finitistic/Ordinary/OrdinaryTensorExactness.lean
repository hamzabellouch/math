import OAI.Algebra.Finitistic.Tensor.IdempotentTensor
import Mathlib.Algebra.Exact.Basic

namespace OAI
noncomputable section
namespace LittleFinitistic
namespace BalancedTensor
universe u
variable {k A M N N' N'' : Type u} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']
variable [AddCommGroup N''] [Module k N''] [Module A N''] [IsScalarTower k A N'']

/-- The actual covariant map in the left-module factor of a balanced tensor. -/
def mapRightTo (f : N →ₗ[A] N') : Tensor k A M N →ₗ[k] Tensor k A M N' :=
  lift ((mk k A M N').compl₁₂ LinearMap.id (f.restrictScalars k)) (by
    intro a m n
    change mk k A M N' (MulOpposite.op a • m) (f n) = mk k A M N' m (f (a • n))
    rw [f.map_smul,balance])

@[simp] theorem mapRightTo_mk (f : N →ₗ[A] N') (m : M) (n : N) :
    mapRightTo (k := k) (M := M) f (mk k A M N m n) = mk k A M N' m (f n) := rfl

end BalancedTensor

namespace IdempotentTensor
universe u
variable {k A N N' N'' : Type u} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']
variable [AddCommGroup N''] [Module k N''] [Module A N''] [IsScalarTower k A N'']
variable (e : A)

def spaceMap (f : N →ₗ[A] N') : leftSpace (k := k) e N →ₗ[k] leftSpace (k := k) e N' where
  toFun x := ⟨f x.val, by
    change e • f x.val = f x.val
    rw [← f.map_smul,x.property]⟩
  map_add' x y := Subtype.ext (f.map_add x.val y.val)
  map_smul' r x := Subtype.ext ((f.restrictScalars k).map_smul r x.val)

theorem tensorEval_naturality (f : N →ₗ[A] N') (z : BalancedTensor.Tensor k A (rightIdeal e) N) :
    tensorEval (k := k) e N' (BalancedTensor.mapRightTo f z) =
      spaceMap (k := k) e f (tensorEval (k := k) e N z) := by
  induction z using BalancedTensor.induction_on with
  | hz => simp only [map_zero]
  | ht m n =>
    apply Subtype.ext
    exact (f.map_smul m.val n).symm
  | ha x y hx hy => simp only [map_add,hx,hy]

/-- Taking an idempotent part preserves exactness, with an explicit projected preimage. -/
theorem spaceMap_exact (he : e*e=e) (f : N →ₗ[A] N') (g : N' →ₗ[A] N'')
    (h : Function.Exact f g) : Function.Exact (spaceMap (k := k) e f) (spaceMap (k := k) e g) := by
  intro x
  constructor
  · intro hx
    have hx' : g x.val = 0 := congrArg Subtype.val hx
    obtain ⟨y,hy⟩ := (h x.val).mp hx'
    refine ⟨⟨e • y, by change e • (e • y) = e • y; rw [← mul_smul,he]⟩, ?_⟩
    apply Subtype.ext
    change f (e • y) = x.val
    rw [f.map_smul,hy,x.property]
  · rintro ⟨y,rfl⟩
    apply Subtype.ext
    exact (h (f y.val)).mpr ⟨y.val,rfl⟩

/-- Tensor with the actual projective eA preserves every exact module sequence. -/
theorem tensor_exact (he : e*e=e) (f : N →ₗ[A] N') (g : N' →ₗ[A] N'')
    (h : Function.Exact f g) :
    Function.Exact (BalancedTensor.mapRightTo (k := k) (M := rightIdeal e) f)
      (BalancedTensor.mapRightTo (k := k) (M := rightIdeal e) g) := by
  intro z
  constructor
  · intro hz
    have hx : spaceMap (k := k) e g (tensorEquiv (k := k) e N' he z) = 0 := by
      change spaceMap (k := k) e g (tensorEval (k := k) e N' z) = 0
      rw [← tensorEval_naturality,hz,map_zero]
    obtain ⟨y,hy⟩ := (spaceMap_exact (k := k) e he f g h _).mp hx
    refine ⟨(tensorEquiv (k := k) e N he).symm y, ?_⟩
    apply (tensorEquiv (k := k) e N' he).injective
    change tensorEval (k := k) e N' (BalancedTensor.mapRightTo f ((tensorEquiv (k := k) e N he).symm y)) =
      tensorEquiv (k := k) e N' he z
    rw [tensorEval_naturality]
    change spaceMap (k := k) e f ((tensorEquiv (k := k) e N he) ((tensorEquiv (k := k) e N he).symm y)) = _
    rw [LinearEquiv.apply_symm_apply,hy]
  · rintro ⟨y,rfl⟩
    induction y using BalancedTensor.induction_on with
    | hz => simp only [map_zero]
    | ht m n =>
      rw [BalancedTensor.mapRightTo_mk,BalancedTensor.mapRightTo_mk,(h (f n)).mpr ⟨n,rfl⟩,map_zero]
    | ha x y hx hy => simp only [map_add,hx,hy,add_zero]
end IdempotentTensor
end LittleFinitistic

end

end OAI
