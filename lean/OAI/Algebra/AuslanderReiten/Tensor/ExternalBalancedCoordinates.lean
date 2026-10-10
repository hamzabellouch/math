import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorCoordinates
import OAI.Algebra.AuslanderReiten.Tensor.ExternalEnvelopingScalar
import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingBalancedMap

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ
variable (M : ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) (N : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ))

abbrev exteriorBimodule (M : ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ))
    (N : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)) := EnvelopingBimodule k (A ⊗[k] B)
  (ExternalTensor.envelopingObject k A B (ExternalTensor.moduleObject k Ae Be M N))

def bimoduleCoordinates : exteriorBimodule k A B M N ≃ₗ[k]
    (EnvelopingBimodule k A M) ⊗[k] (EnvelopingBimodule k B N) :=
  (EnvelopingBimodule.scalarEquiv _).trans
    ((ExternalTensor.envelopingScalarEquiv k A B _).trans
      ((ExternalTensor.moduleScalarCoordinates k Ae Be M N).trans
        (TensorProduct.congr (EnvelopingBimodule.scalarEquiv M).symm
          (EnvelopingBimodule.scalarEquiv N).symm)))

@[simp] theorem bimoduleCoordinates_symm_tmul (m : EnvelopingBimodule k A M)
    (n : EnvelopingBimodule k B N) :
    ((bimoduleCoordinates k A B M N).symm (m ⊗ₜ[k] n)).value =
      m.value ⊗ₜ[k] n.value := rfl

theorem bimoduleCoordinates_right (a : A) (b : B)
    (m : EnvelopingBimodule k A M) (n : EnvelopingBimodule k B N) :
    MulOpposite.op (a ⊗ₜ[k] b) • (bimoduleCoordinates k A B M N).symm (m ⊗ₜ[k] n) =
      (bimoduleCoordinates k A B M N).symm
        ((MulOpposite.op a • m) ⊗ₜ[k] (MulOpposite.op b • n)) := by
  apply EnvelopingBimodule.ext
  change ExternalTensor.representation k Ae Be M N ((ExternalTensor.envelopingEquiv k A B).symm
    (((1 : A) ⊗ₜ[k] (1 : B)) ⊗ₜ[k] MulOpposite.op (a ⊗ₜ[k] b)))
      (m.value ⊗ₜ[k] n.value) = _
  rw [ExternalTensor.envelopingEquiv_symm_tmul]
  rfl

theorem bimoduleCoordinates_left (a : A) (b : B)
    (m : EnvelopingBimodule k A M) (n : EnvelopingBimodule k B N) :
    (a ⊗ₜ[k] b) • (bimoduleCoordinates k A B M N).symm (m ⊗ₜ[k] n) =
      (bimoduleCoordinates k A B M N).symm ((a • m) ⊗ₜ[k] (b • n)) := by
  apply EnvelopingBimodule.ext
  change ExternalTensor.representation k Ae Be M N ((ExternalTensor.envelopingEquiv k A B).symm
    ((a ⊗ₜ[k] b) ⊗ₜ[k] MulOpposite.op ((1 : A) ⊗ₜ[k] (1 : B))))
      (m.value ⊗ₜ[k] n.value) = _
  rw [ExternalTensor.envelopingEquiv_symm_tmul]
  rfl

end ArExplicit.ExternalBalanced

end

end OAI
