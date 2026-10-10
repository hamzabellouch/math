import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingEvaluationFunctor
import OAI.Algebra.AuslanderReiten.Tensor.ExternalBalancedNaturality

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
variable {M M' : ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)}
  {N N' : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)}

private theorem balancedMap_identity {S : Type u} [Ring S] [Algebra k S]
    {L L' : ModuleCat.{u} (S ⊗[k] Sᵐᵒᵖ)} (Z : ModuleCat.{u} S) (f : L ⟶ L') :
    balancedMap f (𝟙 Z) = EnvelopingBimodule.tensorMap Z f := by
  unfold balancedMap
  change (BalancedTensor.mapRight (k := k) (S := S) (LinearMap.id : Z →ₗ[S] Z)).comp _ = _
  rw [BalancedTensor.mapRight_id, LinearMap.id_comp]

theorem shuffle_natural_fixed (f : M ⟶ M') (g : N ⟶ N') :
    (EnvelopingBimodule.evaluationFunctor k (A ⊗[k] B)
      (ExternalTensor.moduleObject k A B X Y)).map (exteriorMap f g) ≫
        (shuffle k A B M' N' X Y).toModuleIso.hom =
    (shuffle k A B M N X Y).toModuleIso.hom ≫
      ExternalTensor.mapHom k A B
        ((EnvelopingBimodule.evaluationFunctor k A X).map f)
        ((EnvelopingBimodule.evaluationFunctor k B Y).map g) := by
  apply ModuleCat.hom_ext
  have h := shuffle_natural (k := k) f g (𝟙 X) (𝟙 Y)
  rw [ExternalTensor.mapHom_id, balancedMap_identity, balancedMap_identity,
    balancedMap_identity] at h
  exact h

end ArExplicit.ExternalBalanced

end

end OAI
