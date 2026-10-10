import OAI.Algebra.AuslanderReiten.Tensor.TwistedTensorResolution
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorAugmentation
import OAI.Algebra.AuslanderReiten.Evaluation.TensorEndpointEvaluation

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
local notation "R" => T k q
local notation "Te" => AbsoluteBar.Enveloping k R

theorem sourceBaseEquiv_barUnit :
    sourceBaseEquiv q H (Submodule.Quotient.mk (tensorBarUnit q H)) =
      (⟨1⟩ : TwistedBimodule k (A k q) (sourceTwist q H)) := by
  change twistedBarTensorBimoduleEquiv k R R (TrivialExtension.twist H) (TrivialExtension.twist H)
    ((ExternalTensor.augmentation k Te Te
      (AbsoluteBar.twistedResolution k R (TrivialExtension.twist H))
      (AbsoluteBar.twistedResolution k R (TrivialExtension.twist H))).f 0
        (tensorBarUnit q H)) = _
  unfold tensorBarUnit
  erw [ExternalTensor.augmentation_insert k Te Te
    (AbsoluteBar.twistedResolution k R (TrivialExtension.twist H))
    (AbsoluteBar.twistedResolution k R (TrivialExtension.twist H))]
  change twistedBarTensorBimoduleEquiv k R R (TrivialExtension.twist H) (TrivialExtension.twist H)
    (ExternalTensor.map k Te Te
      ((AbsoluteBar.twistedResolution k R (TrivialExtension.twist H)).π.f 0).hom
      ((AbsoluteBar.twistedResolution k R (TrivialExtension.twist H)).π.f 0).hom
      (twistedBarUnit q H ⊗ₜ[k] twistedBarUnit q H)) = _
  erw [ExternalTensor.map_tmul]
  have hu : ((AbsoluteBar.twistedResolution k R (TrivialExtension.twist H)).π.f 0).hom
      (twistedBarUnit q H) = (show AbsoluteBar.twistedObject k R (TrivialExtension.twist H) 0 from (1 : R)) := by
    change ((AbsoluteBar.twistedAugmentation k R (TrivialExtension.twist H)).f 0).hom _ = _
    rw [AbsoluteBar.twistedAugmentation_zero]
    change (1 : R) * 1 = 1
    exact one_mul 1
  simp only [hu]
  apply TwistedBimodule.ext
  change (1 : R) ⊗ₜ[k] (1 : R) = (1 : A k q)
  rfl

end ArExplicit.T

end

end OAI
