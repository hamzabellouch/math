import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorModule
import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtensionComplete

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower

def moduleScalarCoordinates (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) :
    moduleObject k A B M N ≃ₗ[k] (M ⊗[k] N) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change representation k A B M N (algebraMap k (A ⊗[k] B) a) x = a • (show M ⊗[k] N from x)
    rw [AlgHom.commutes]
    rfl

end ArExplicit.ExternalTensor

end

end OAI
