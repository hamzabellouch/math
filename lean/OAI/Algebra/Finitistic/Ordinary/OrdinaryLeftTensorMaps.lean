import OAI.Algebra.Finitistic.Ordinary.OrdinaryAssociativeTensorModules
import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorBimap

namespace OAI
noncomputable section
namespace LittleFinitistic.LeftTensor
universe u
variable {k A S M M' N N' : Type u} [Field k] [Ring A] [Ring S] [Algebra k A] [Algebra k S]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
  [Module S M] [IsScalarTower k S M] [SMulCommClass S Aᵐᵒᵖ M]
variable [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M'] [IsScalarTower k Aᵐᵒᵖ M']
  [Module S M'] [IsScalarTower k S M'] [SMulCommClass S Aᵐᵒᵖ M']
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']

/-- The actual balanced bimap retains the outside left action. -/
def bimap (f : M →ₗ[Aᵐᵒᵖ] M') (hf : ∀ (s : S) m, f (s • m) = s • f m)
    (g : N →ₗ[A] N') : LeftTensor k A S M N →ₗ[S] LeftTensor k A S M' N' where
  __ := (BalancedTensor.bimap (k := k) f g).toAddHom
  map_smul' s z := by
    change BalancedTensor.bimap (k := k) f g (action k S A M N s z) =
      action k S A M' N' s (BalancedTensor.bimap (k := k) f g z)
    induction z using BalancedTensor.induction_on with
    | hz =>
      exact ((BalancedTensor.bimap (k := k) f g).comp (action k S A M N s)).map_zero.trans
        (((action k S A M' N' s).comp (BalancedTensor.bimap (k := k) f g)).map_zero).symm
    | ht m n =>
      change BalancedTensor.mk k A M' N' (f (s • m)) (g n) =
        BalancedTensor.mk k A M' N' (s • f m) (g n)
      rw [hf]
    | ha x y hx hy =>
      exact (((BalancedTensor.bimap (k := k) f g).comp (action k S A M N s)).map_add x y).trans
        ((congrArg₂ (· + ·) hx hy).trans
          (((action k S A M' N' s).comp (BalancedTensor.bimap (k := k) f g)).map_add x y).symm)

@[simp] theorem bimap_mk (f : M →ₗ[Aᵐᵒᵖ] M') (hf : ∀ (s : S) m, f (s • m) = s • f m)
    (g : N →ₗ[A] N') (m : M) (n : N) :
    bimap f hf g (mk k S A M N m n) = mk k S A M' N' (f m) (g n) := rfl
end LittleFinitistic.LeftTensor

end

end OAI
