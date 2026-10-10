import OAI.Algebra.AuslanderReiten.Ext.ExternalNativeBarAugmentation
import OAI.Algebra.AuslanderReiten.Ext.ExternalRegularEvaluation

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B M N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [CharP k 2] [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N]
local notation "XM" => ModuleCat.of A M
local notation "YN" => ModuleCat.of B N
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ
local instance : Module k (ExternalTensor.canonicalTensorObject k A B M N) :=
  moduleCatBaseModule (k := k) (R := A ⊗[k] B) _
local instance : IsScalarTower k (A ⊗[k] B) (ExternalTensor.canonicalTensorObject k A B M N) :=
  moduleCatBaseTower (k := k) (R := A ⊗[k] B) _
private abbrev eval := EnvelopingBimodule.evaluationFunctor k (A ⊗[k] B)
  (ExternalTensor.canonicalTensorObject k A B M N)

theorem nativeTotalBarIso_regularAugmentation :
    (nativeTotalBarIso k A B M N).hom.f 0 ≫
      (ExternalTensor.augmentation k A B (ModuleBar.nativeResolution k A M)
        (ModuleBar.nativeResolution k B N)).f 0 =
    (eval k A B M N).map
      ((ExternalTensor.envelopingFunctor k A B).map
        ((ExternalTensor.augmentation k Ae Be (AbsoluteBar.resolution k A)
          (AbsoluteBar.resolution k B)).f 0) ≫ (barTensorZeroEquiv k A B).toModuleIso.hom) ≫
      (BarBalanced.nativeEndpointIso k (A ⊗[k] B)
        (ExternalTensor.canonicalTensorObject k A B M N)).hom := by
  rw [nativeTotalBarIso_augmentation, regularEndpoint_eq]
  conv_rhs => erw [Functor.map_comp]
  erw [Category.assoc]
  rfl

end ArExplicit.ExternalBalanced

end

end OAI
