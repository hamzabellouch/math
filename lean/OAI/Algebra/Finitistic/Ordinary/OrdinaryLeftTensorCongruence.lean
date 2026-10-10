import OAI.Algebra.Finitistic.Ordinary.OrdinaryLeftTensorMaps
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBalancedCongruence

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

/-- Actual balanced tensor congruence retaining the outside left action. -/
def congr (f : M ≃ₗ[Aᵐᵒᵖ] M') (hf : ∀ (s : S) m, f (s • m) = s • f m)
    (g : N ≃ₗ[A] N') : LeftTensor k A S M N ≃ₗ[S] LeftTensor k A S M' N' where
  __ := bimap f.toLinearMap hf g.toLinearMap
  invFun := (BalancedTensor.congr (k := k) f g).symm
  left_inv := (BalancedTensor.congr (k := k) f g).left_inv
  right_inv := (BalancedTensor.congr (k := k) f g).right_inv
end LittleFinitistic.LeftTensor

end

end OAI
