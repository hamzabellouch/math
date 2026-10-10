import OAI.Algebra.Finitistic.Tensor.BalancedTensorMaps

namespace OAI
noncomputable section
namespace LittleFinitistic.IdempotentTensor
universe u v w
variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
variable (e : A)

/-- The actual projective right ideal eA, presented as the fixed points of left multiplication. -/
def rightIdeal : Submodule Aᵐᵒᵖ A where
  carrier := {a | e*a=a}
  zero_mem' := mul_zero e
  add_mem' ha hb := by change e*(_+_)=_+_; rw [mul_add,ha,hb]
  smul_mem' b a ha := by
    change e*(a*b.unop)=a*b.unop
    rw [← mul_assoc,ha]

variable (N : Type w) [AddCommGroup N] [Module k N] [Module A N]
  [IsScalarTower k A N]

/-- The vertex part eN, without assuming e is central. -/
def leftSpace : Submodule k N where
  carrier := {n | e • n = n}
  zero_mem' := smul_zero e
  add_mem' ha hb := by change e • (_+_) = _+_; rw [smul_add,ha,hb]
  smul_mem' c n hn := by change e • (c • n) = c • n; rw [smul_comm e c,hn]

def productEval : rightIdeal e →ₗ[k] N →ₗ[k] leftSpace (k := k) e N where
  toFun a :=
    { toFun := fun n => ⟨a.val • n, by change e • (a.val • n) = a.val • n; rw [← mul_smul,a.property]⟩
      map_add' n m := Subtype.ext (smul_add a.val n m)
      map_smul' c n := Subtype.ext (smul_comm a.val c n) }
  map_add' a b := by ext n; exact add_smul a.val b.val n
  map_smul' c a := by ext n; exact smul_assoc c a.val n

/-- The natural map eA tensor_A N → eN. -/
def tensorEval : BalancedTensor.Tensor k A (rightIdeal e) N →ₗ[k] leftSpace (k := k) e N :=
  BalancedTensor.lift (productEval (k := k) e N) (by
    intro a m n
    apply Subtype.ext
    exact mul_smul m.val a n)

@[simp] theorem tensorEval_mk (m : rightIdeal e) (n : N) :
    (tensorEval (k := k) e N (BalancedTensor.mk k A (rightIdeal e) N m n)).val = m.val • n := rfl

variable (he : e*e=e)

def tensorInv : leftSpace (k := k) e N →ₗ[k] BalancedTensor.Tensor k A (rightIdeal e) N :=
  (BalancedTensor.mk k A (rightIdeal e) N ⟨e,he⟩).comp (leftSpace (k := k) e N).subtype

@[simp] theorem tensorEval_tensorInv (n : leftSpace (k := k) e N) :
    tensorEval (k := k) e N (tensorInv (k := k) e N he n) = n := by
  apply Subtype.ext
  exact n.property

@[simp] theorem tensorInv_tensorEval (z : BalancedTensor.Tensor k A (rightIdeal e) N) :
    tensorInv (k := k) e N he (tensorEval (k := k) e N z) = z := by
  induction z using BalancedTensor.induction_on with
  | hz => simp
  | ht m n =>
    change BalancedTensor.mk k A (rightIdeal e) N ⟨e,he⟩ (m.val • n) =
      BalancedTensor.mk k A (rightIdeal e) N m n
    rw [← BalancedTensor.balance]
    have hm : MulOpposite.op m.val • (⟨e,he⟩ : rightIdeal e) = m := by
      apply Subtype.ext
      exact m.property
    rw [hm]
  | ha a b h₁ h₂ => simp [h₁,h₂]

/-- Evaluation on a vertex projective is its actual vertex space. -/
def tensorEquiv : BalancedTensor.Tensor k A (rightIdeal e) N ≃ₗ[k] leftSpace (k := k) e N where
  __ := tensorEval (k := k) e N
  invFun := tensorInv (k := k) e N he
  left_inv := tensorInv_tensorEval (k := k) e N he
  right_inv := tensorEval_tensorInv (k := k) e N he
end LittleFinitistic.IdempotentTensor

end

end OAI
