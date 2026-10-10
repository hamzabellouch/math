import OAI.Algebra.AuslanderReiten.Evaluation.CanonicalRegularMap
import OAI.Algebra.AuslanderReiten.Bar.BarTensorRegularIsoCoordinates
import OAI.Algebra.AuslanderReiten.Tensor.ExternalBalancedCoordinates

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)

theorem regularTensorMap_tmul
    (z : exteriorBimodule k A B (AbsoluteBar.moduleObject k A 0)
      (AbsoluteBar.moduleObject k B 0)) (w : ExternalTensor.moduleObject k A B X Y) :
    type_of% (BarBalanced.regularMap_tmul k (A ⊗[k] B)
      (ExternalTensor.moduleObject k A B X Y)
      (ExternalTensor.envelopingObject k A B
        (ExternalTensor.moduleObject k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ)
          (AbsoluteBar.moduleObject k A 0) (AbsoluteBar.moduleObject k B 0)))
      (barTensorZeroEquiv k A B).toModuleIso.hom z w) :=
  BarBalanced.regularMap_tmul k (A ⊗[k] B)
    (ExternalTensor.moduleObject k A B X Y)
    (ExternalTensor.envelopingObject k A B
      (ExternalTensor.moduleObject k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ)
        (AbsoluteBar.moduleObject k A 0) (AbsoluteBar.moduleObject k B 0)))
    (barTensorZeroEquiv k A B).toModuleIso.hom z w

end ArExplicit.ExternalBalanced

end

end OAI
