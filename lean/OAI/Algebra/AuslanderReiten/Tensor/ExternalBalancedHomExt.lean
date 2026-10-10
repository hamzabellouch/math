import OAI.Algebra.AuslanderReiten.Ext.ExternalEvaluationTerms
import OAI.Algebra.AuslanderReiten.Tensor.BalancedFourAddExt

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (M : ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) (N : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ))
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B) (Z : ModuleCat.{u} (A ⊗[k] B))

theorem exterior_hom_ext
    (f g : (productEvaluation k A B X Y).obj
      (ExternalTensor.moduleObject k (A ⊗[k] Aᵐᵒᵖ) (B ⊗[k] Bᵐᵒᵖ) M N) ⟶ Z)
    (h : ∀ (a : EnvelopingBimodule k A M) (b : EnvelopingBimodule k B N) (x : X) (y : Y),
      f (BalancedTensor.tmul ((bimoduleCoordinates k A B M N).symm (a ⊗ₜ[k] b))
        ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))) =
      g (BalancedTensor.tmul ((bimoduleCoordinates k A B M N).symm (a ⊗ₜ[k] b))
        ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y)))) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  exact fourfold_add_hom_ext (k := k) (A := A) (B := B) (Z := Z)
    (bimoduleCoordinates k A B M N) (ExternalTensor.moduleScalarCoordinates k A B X Y)
    f.hom.toAddMonoidHom g.hom.toAddMonoidHom h

end ArExplicit.ExternalBalanced

end

end OAI
