import OAI.Algebra.AuslanderReiten.Bar.ExternalBarEvaluation
import OAI.Algebra.AuslanderReiten.Ext.ExternalEvaluationAugmentation
import OAI.Algebra.AuslanderReiten.Bar.NativeBarAugmentation

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

theorem nativeTotalBarIso_augmentation :
    (nativeTotalBarIso k A B M N).hom.f 0 ≫
      (ExternalTensor.augmentation k A B (ModuleBar.nativeResolution k A M)
        (ModuleBar.nativeResolution k B N)).f 0 =
    (productEvaluation k A B XM YN).map
      ((ExternalTensor.augmentation k Ae Be (AbsoluteBar.resolution k A)
        (AbsoluteBar.resolution k B)).f 0) ≫
      totalEndpointMap k A B XM YN (BarBalanced.nativeEndpointIso k A M).hom
        (BarBalanced.nativeEndpointIso k B N).hom :=
  totalEvaluation_augmentation k A B XM YN (AbsoluteBar.resolution k A)
    (AbsoluteBar.resolution k B) (ModuleBar.nativeResolution k A M) (ModuleBar.nativeResolution k B N)
    (BarBalanced.nativeComplexIso k A M) (BarBalanced.nativeComplexIso k B N)
    (BarBalanced.nativeEndpointIso k A M).hom (BarBalanced.nativeEndpointIso k B N).hom
    (BarBalanced.nativeComplexIso_augmentation k A M) (BarBalanced.nativeComplexIso_augmentation k B N)

end ArExplicit.ExternalBalanced

end

end OAI
