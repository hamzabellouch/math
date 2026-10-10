import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingBalancedMap
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorEquiv

namespace OAI

noncomputable section
namespace ArExplicit.EnvelopingBimodule
open CategoryTheory
open scoped TensorProduct
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {M N : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)}
variable [Module k M] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) M]
variable [Module k N] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) N]
variable (e : M ≃ₗ[R ⊗[k] Rᵐᵒᵖ] N)

def scalarCongr : EnvelopingBimodule k R M ≃ₗ[k] EnvelopingBimodule k R N where
  toFun x := ⟨e x.value⟩
  invFun y := ⟨e.symm y.value⟩
  left_inv x := by ext; exact e.symm_apply_apply x.value
  right_inv y := by ext; exact e.apply_symm_apply y.value
  map_add' x y := by ext; exact e.map_add _ _
  map_smul' c x := by ext; exact (e.restrictScalars k).map_smul c x.value

@[simp] theorem scalarCongr_left (a : R) (x : EnvelopingBimodule k R M) :
    scalarCongr e (a • x) = a • scalarCongr e x := by
  ext
  exact e.map_smul (a ⊗ₜ[k] (1 : Rᵐᵒᵖ)) x.value

@[simp] theorem scalarCongr_right (a : Rᵐᵒᵖ) (x : EnvelopingBimodule k R M) :
    scalarCongr e (a • x) = a • scalarCongr e x := by
  ext
  exact e.map_smul ((1 : R) ⊗ₜ[k] a) x.value

variable (X : ModuleCat.{u} R) [Module k X]

def tensorCongr : BalancedTensor k R (EnvelopingBimodule k R M) X ≃ₗ[R]
    BalancedTensor k R (EnvelopingBimodule k R N) X :=
  BalancedTensor.congrLeft (scalarCongr e) (LinearEquiv.refl k X)
    (scalarCongr_right e) (fun _ _ => rfl) (scalarCongr_left e)

@[simp] theorem tensorCongr_tmul (m : EnvelopingBimodule k R M) (x : X) :
    tensorCongr e X (BalancedTensor.tmul m x) =
      BalancedTensor.tmul (⟨e m.value⟩ : EnvelopingBimodule k R N) x := rfl

end ArExplicit.EnvelopingBimodule

end

end OAI
