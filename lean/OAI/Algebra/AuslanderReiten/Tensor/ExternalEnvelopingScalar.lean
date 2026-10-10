import OAI.Algebra.AuslanderReiten.Tensor.ExternalEnveloping
import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtensionComplete

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower

def envelopingScalarEquiv (M : ModuleCat.{u} (ProductEnveloping k A B)) :
    envelopingObject k A B M ≃ₗ[k] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change (envelopingEquiv k A B).symm (algebraMap k (EnvelopingProduct k A B) a) • (show M from x) =
      a • (show M from x)
    rw [AlgEquiv.commutes, algebraMap_smul]

end ArExplicit.ExternalTensor

end

end OAI
