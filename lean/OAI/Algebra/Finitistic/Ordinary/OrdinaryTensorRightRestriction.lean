import OAI.Algebra.Finitistic.Ordinary.OrdinaryTwoSidedTensor
import OAI.Algebra.Finitistic.Ordinary.OrdinaryAssociativeTensorModules
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.TwoSidedTensor
universe u
variable (k A B S M N : Type u) [Field k] [Ring A] [Ring B] [Ring S]
  [Algebra k A] [Algebra k B] [Algebra k S]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
  [Module S M] [IsScalarTower k S M] [SMulCommClass S Aᵐᵒᵖ M]
variable [AddCommGroup N] [Module k N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]

local instance : SMulCommClass Bᵐᵒᵖ A N := ⟨fun b a n => (smul_comm a b n).symm⟩

/-- The actual outside right action obtained by restricting the enveloping action. -/
abbrev rightRestriction : ModuleCat.{u} Bᵐᵒᵖ :=
  (ModuleCat.restrictScalars (Algebra.TensorProduct.includeRight (R := k) (A := S) (B := Bᵐᵒᵖ)).toRingHom).obj
    (ModuleCat.of (S ⊗[k] Bᵐᵒᵖ) (TwoSidedTensor k A S Bᵐᵒᵖ M N))

/-- The one-sided right tensor action equals the restriction of the genuine two-sided action. -/
def rightActionEquiv : RightTensor k A B M N ≃ₗ[Bᵐᵒᵖ] rightRestriction k A B S M N where
  toFun x := x
  invFun x := x
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' r x := by
    let F : BalancedTensor.Tensor k A M N →ₗ[k] BalancedTensor.Tensor k A M N :=
      RightTensor.action k A B M N r
    let G : BalancedTensor.Tensor k A M N →ₗ[k] BalancedTensor.Tensor k A M N :=
      TwoSidedTensor.action k A S Bᵐᵒᵖ M N ((1:S) ⊗ₜ[k] r)
    have h : F = G := by
      apply BalancedTensor.ext
      intro m n
      change BalancedTensor.mk k A M N m (r • n) = BalancedTensor.mk k A M N ((1:S) • m) (r • n)
      rw [one_smul]
    exact congrArg (fun f => f x) h

end LittleFinitistic.TwoSidedTensor

end

end OAI
