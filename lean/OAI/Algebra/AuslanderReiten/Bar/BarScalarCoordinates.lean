import OAI.Algebra.AuslanderReiten.Bar.BarBimodule
import OAI.Algebra.AuslanderReiten.BaseChange.ScalarExtensionComplete

namespace OAI

noncomputable section
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower

def scalarCoordinates (n : ℕ) : moduleObject k R n ≃ₗ[k] object k R n where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change representation k R n (algebraMap k (Enveloping k R) a)
      (show object k R n from x) = a • (show object k R n from x)
    rw [AlgHom.commutes]
    rfl

end ArExplicit.AbsoluteBar

end

end OAI
