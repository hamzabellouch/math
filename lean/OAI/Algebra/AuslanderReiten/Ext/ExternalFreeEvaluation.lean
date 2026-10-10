import OAI.Algebra.AuslanderReiten.Ext.ExternalEvaluationTerms
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorScalarPure
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorRegular

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
variable (f : (EnvelopingBimodule.evaluationFunctor k A X).obj M ⟶ ModuleCat.of A A)
  (g : (EnvelopingBimodule.evaluationFunctor k B Y).obj N ⟶ ModuleCat.of B B)

def freeEvaluation : (productEvaluation k A B X Y).obj
    (ExternalTensor.moduleObject k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) M N) ⟶
      ModuleCat.of (A ⊗[k] B) (A ⊗[k] B) :=
  (shuffle k A B M N X Y).toModuleIso.hom ≫ ExternalTensor.mapHom k A B f g ≫
    (ExternalTensor.canonicalTensorIso k A B A B).hom ≫
      (ExternalTensor.regularEquiv k A B).toModuleIso.hom

theorem freeEvaluation_pure (a : EnvelopingBimodule k A M)
    (b : EnvelopingBimodule k B N) (x : X) (y : Y) :
    freeEvaluation k A B M N X Y f g (BalancedTensor.tmul
      ((bimoduleCoordinates k A B M N).symm (a ⊗ₜ[k] b))
      ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))) =
        (f (BalancedTensor.tmul a x)) ⊗ₜ[k] (g (BalancedTensor.tmul b y)) := by
  change (ExternalTensor.mapHom k A B f g ≫
    (ExternalTensor.canonicalTensorIso k A B A B).hom ≫
      (ExternalTensor.regularEquiv k A B).toModuleIso.hom)
        (shuffle k A B M N X Y (BalancedTensor.tmul
          ((bimoduleCoordinates k A B M N).symm (a ⊗ₜ[k] b))
          ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y)))) = _
  rw [shuffle_pure]
  change ExternalTensor.regularEquiv k A B ((ExternalTensor.canonicalTensorIso k A B A B).hom
    (ExternalTensor.canonicalTmul k A B A B
      (f (BalancedTensor.tmul a x)) (g (BalancedTensor.tmul b y)))) = _
  rw [ExternalTensor.canonicalTensorIso_tmul]
  rfl

end ArExplicit.ExternalBalanced

end

end OAI
