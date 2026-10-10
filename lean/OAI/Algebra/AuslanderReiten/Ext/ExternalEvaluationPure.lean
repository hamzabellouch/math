import OAI.Algebra.AuslanderReiten.Ext.ExternalFreeEvaluation

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (M : ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) (N : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ))
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B) (Z : ModuleCat.{u} (A ⊗[k] B))
variable (f : (EnvelopingBimodule.evaluationFunctor k A X).obj M ⟶ U)
  (g : (EnvelopingBimodule.evaluationFunctor k B Y).obj N ⟶ V)
  (h : ExternalTensor.moduleObject k A B U V ⟶ Z)

theorem postShuffle_pure (a : EnvelopingBimodule k A M)
    (b : EnvelopingBimodule k B N) (x : X) (y : Y) :
    ((shuffle k A B M N X Y).toModuleIso.hom ≫ ExternalTensor.mapHom k A B f g ≫ h)
      (BalancedTensor.tmul
        ((bimoduleCoordinates k A B M N).symm (a ⊗ₜ[k] b))
        ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))) =
      h (ExternalTensor.canonicalTmul k A B U V
        (f (BalancedTensor.tmul a x)) (g (BalancedTensor.tmul b y))) := by
  change h (ExternalTensor.mapHom k A B f g (shuffle k A B M N X Y
    (BalancedTensor.tmul
      ((bimoduleCoordinates k A B M N).symm (a ⊗ₜ[k] b))
      ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))))) = _
  rw [shuffle_pure]
  rfl

end ArExplicit.ExternalBalanced

end

end OAI
