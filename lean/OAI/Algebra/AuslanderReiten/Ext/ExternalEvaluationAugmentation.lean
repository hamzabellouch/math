import OAI.Algebra.AuslanderReiten.Ext.ExternalEvaluationDifferential
import OAI.Algebra.AuslanderReiten.Ext.ExternalComplexIso
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorAugmentation

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
variable {U : ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)} {V : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)}
variable (P : ProjectiveResolution U) (Q : ProjectiveResolution V)
variable (P' : ProjectiveResolution X) (Q' : ProjectiveResolution Y)
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ
local notation "EA" => EnvelopingBimodule.evaluationFunctor k A X
local notation "EB" => EnvelopingBimodule.evaluationFunctor k B Y
local notation "E" => productEvaluation k A B X Y

def totalEndpointMap (e : (EA).obj U ⟶ X) (f : (EB).obj V ⟶ Y) :
    (E).obj (ExternalTensor.moduleObject k Ae Be U V) ⟶
      ExternalTensor.moduleObject k A B X Y :=
  (shuffle k A B U V X Y).toModuleIso.hom ≫ ExternalTensor.mapHom k A B e f

theorem totalEvaluation_augmentation
    (a : factorEvaluation k X P.complex ≅ P'.complex)
    (b : factorEvaluation k Y Q.complex ≅ Q'.complex)
    (e : (EA).obj U ⟶ X) (f : (EB).obj V ⟶ Y)
    (ha : a.hom.f 0 ≫ P'.π.f 0 = (EA).map (P.π.f 0) ≫ e)
    (hb : b.hom.f 0 ≫ Q'.π.f 0 = (EB).map (Q.π.f 0) ≫ f) :
    (totalEvaluationIso k A B X Y P.complex Q.complex ≪≫
      ExternalTensor.complexIso k A B a b).hom.f 0 ≫
        (ExternalTensor.augmentation k A B P' Q').f 0 =
    (E).map ((ExternalTensor.augmentation k Ae Be P Q).f 0) ≫
      totalEndpointMap k A B X Y e f := by
  apply evaluatedTotal_hom_ext k A B X Y P.complex Q.complex
  intro i j hij
  have hi : i=0 := by omega
  have hj : j=0 := by omega
  subst i; subst j
  change (E).map (ExternalTensor.inclusion k Ae Be P.complex Q.complex 0 0 0 hij) ≫
      (((totalEvaluationTermIso k A B X Y P.complex Q.complex 0).hom ≫
        (ExternalTensor.complexMap k A B a.hom b.hom).f 0) ≫
          (ExternalTensor.augmentation k A B P' Q').f 0) = _
  erw [Category.assoc, ← Category.assoc,
    inclusion_totalEvaluationTermIso k A B X Y P.complex Q.complex 0 0 0 hij]
  erw [Category.assoc, ExternalTensor.inclusion_complexMap_assoc,
    ExternalTensor.inclusion_augmentation k A B P' Q',
    ← ExternalTensor.mapHom_comp k A B (a.hom.f 0) (P'.π.f 0) (b.hom.f 0) (Q'.π.f 0), ha, hb,
    ExternalTensor.mapHom_comp k A B ((EA).map (P.π.f 0)) e ((EB).map (Q.π.f 0)) f]
  symm
  erw [← Category.assoc, ← (E).map_comp, ExternalTensor.inclusion_augmentation k Ae Be P Q]
  change (E).map (ExternalTensor.mapHom k Ae Be (P.π.f 0) (Q.π.f 0)) ≫
      ((shuffle k A B U V X Y).toModuleIso.hom ≫ ExternalTensor.mapHom k A B e f) = _
  erw [← Category.assoc, shuffle_natural_fixed, Category.assoc]

end ArExplicit.ExternalBalanced

end

end OAI
