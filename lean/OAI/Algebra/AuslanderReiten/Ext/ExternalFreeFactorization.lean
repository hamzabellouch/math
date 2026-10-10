import OAI.Algebra.AuslanderReiten.Ext.ExternalFreeEvaluation

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
private theorem replace_product {C : Type*} [Category C]
    {P Q R S T : C} (d : P ⟶ Q) (p : Q ⟶ R) (q : R ⟶ S)
    (r : S ⟶ T) (s : Q ⟶ S) (h : s = p ≫ q) :
    d ≫ p ≫ q ≫ r = d ≫ s ≫ r := by
  rw [h, Category.assoc]

universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (M : ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) (N : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ))
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)
variable (a : (EnvelopingBimodule.evaluationFunctor k A X).obj M ⟶ U)
  (b : (EnvelopingBimodule.evaluationFunctor k B Y).obj N ⟶ V)
variable (f : U ⟶ ModuleCat.of A A) (g : V ⟶ ModuleCat.of B B)

theorem freeEvaluation_factorization :
    (shuffle k A B M N X Y).toModuleIso.hom ≫ ExternalTensor.mapHom k A B a b ≫
      ExternalTensor.mapHom k A B f g ≫
        (ExternalTensor.canonicalTensorIso k A B A B).hom ≫
          (ExternalTensor.regularEquiv k A B).toModuleIso.hom =
    freeEvaluation k A B M N X Y (a ≫ f) (b ≫ g) :=
  replace_product (shuffle k A B M N X Y).toModuleIso.hom
    (ExternalTensor.mapHom k A B a b) (ExternalTensor.mapHom k A B f g)
    ((ExternalTensor.canonicalTensorIso k A B A B).hom ≫
      (ExternalTensor.regularEquiv k A B).toModuleIso.hom)
    (ExternalTensor.mapHom k A B (a ≫ f) (b ≫ g))
    (ExternalTensor.mapHom_comp k A B a f b g)

end ArExplicit.ExternalBalanced

end

end OAI
