import OAI.Algebra.Finitistic.Tensor.BalancedTensorMaps
import Mathlib.RingTheory.TensorProduct.Maps

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.BalancedTensor
universe u
variable {k A M N S T : Type u} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- Tensor an actual left-module homomorphism with the identity. -/
def mapRight (f : N →ₗ[A] N) : Tensor k A M N →ₗ[k] Tensor k A M N :=
  lift ((mk k A M N).compl₁₂ LinearMap.id (f.restrictScalars k)) (by
    intro a m n
    change mk k A M N (MulOpposite.op a • m) (f n) = mk k A M N m (f (a • n))
    rw [f.map_smul, balance])

omit [IsScalarTower k Aᵐᵒᵖ M] in
@[simp] theorem mapRight_mk (f : N →ₗ[A] N) (m : M) (n : N) :
    mapRight (k := k) (M := M) f (mk k A M N m n) = mk k A M N m (f n) := rfl

variable [Ring S] [Algebra k S] [Module S M] [IsScalarTower k S M]
  [SMulCommClass S Aᵐᵒᵖ M]

/-- The left coefficient action is induced from the first balanced-tensor factor. -/
def leftAction : S →ₐ[k] Module.End k (Tensor k A M N) where
  toFun s := mapLeft N (Algebra.lsmul k Aᵐᵒᵖ M s)
  map_one' := by apply ext; intro m n; simp
  map_mul' s t := by apply ext; intro m n; simp
  map_zero' := by apply ext; intro m n; simp
  map_add' s t := by apply ext; intro m n; simp
  commutes' r := by apply ext; intro m n; simp

omit [IsScalarTower k A N] in
@[simp] theorem leftAction_mk (s : S) (m : M) (n : N) :
    leftAction (k := k) (A := A) (N := N) s (mk k A M N m n) = mk k A M N (s • m) n := rfl

variable [Ring T] [Algebra k T] [Module T N] [IsScalarTower k T N]
  [SMulCommClass T A N]

/-- The right coefficient action is induced from the second balanced-tensor factor. -/
def rightAction : T →ₐ[k] Module.End k (Tensor k A M N) where
  toFun t := mapRight (Algebra.lsmul k A N t)
  map_one' := by apply ext; intro m n; simp
  map_mul' s t := by apply ext; intro m n; simp
  map_zero' := by apply ext; intro m n; simp
  map_add' s t := by apply ext; intro m n; simp
  commutes' r := by apply ext; intro m n; simp

omit [IsScalarTower k Aᵐᵒᵖ M] in
@[simp] theorem rightAction_mk (t : T) (m : M) (n : N) :
    rightAction (k := k) (A := A) (M := M) t (mk k A M N m n) = mk k A M N m (t • n) := rfl

/-- Both outside actions on a balanced tensor, combined without forgetting either factor. -/
def bimoduleAction : (S ⊗[k] T) →ₐ[k] Module.End k (Tensor k A M N) :=
  Algebra.TensorProduct.lift (leftAction (k := k) (A := A) (M := M) (N := N))
    (rightAction (k := k) (A := A) (M := M) (N := N)) (by
      intro s t
      apply ext
      intro m n
      rfl)

@[simp] theorem bimoduleAction_tmul_mk (s : S) (t : T) (m : M) (n : N) :
    bimoduleAction (k := k) (A := A) (M := M) (N := N) (s ⊗ₜ[k] t) (mk k A M N m n) =
      mk k A M N (s • m) (t • n) := rfl
end LittleFinitistic.BalancedTensor

end

end OAI
