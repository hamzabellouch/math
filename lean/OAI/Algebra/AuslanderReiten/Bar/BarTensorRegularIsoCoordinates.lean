import OAI.Algebra.AuslanderReiten.Bar.BarTensorRegularCoordinates

namespace OAI

noncomputable section
namespace ArExplicit
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower

@[simp] theorem barTensorZeroIso_tmul (a : AbsoluteBar.moduleObject k A 0)
    (b : AbsoluteBar.moduleObject k B 0) :
    (barTensorZeroEquiv k A B).toModuleIso.hom (a ⊗ₜ[k] b) =
      (show A from a) ⊗ₜ[k] (show B from b) :=
  barTensorZeroEquiv_tmul k A B a b

end ArExplicit

end

end OAI
