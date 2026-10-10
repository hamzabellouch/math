import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorExt
import OAI.Algebra.AuslanderReiten.Ext.NatCubicExt

namespace OAI

noncomputable section
namespace ArExplicit.ModuleBar
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
universe u
variable (k R S M N : Type u) [Field k] [CharP k 2]
  [Ring R] [Algebra k R] [Module.Finite k R] [Ring S] [Algebra k S] [Module.Finite k S]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [Module.Finite k M]
  [AddCommGroup N] [Module S N] [Module k N] [IsScalarTower k S N] [Module.Finite k N]
variable [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
  [HasDerivedCategory (ModuleCat.{u} (R ⊗[k] S))]
variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)
variable (r : AbsoluteBar.Cochain3 k S) (hr : AbsoluteBar.IsCocycle3 k S r)

omit [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)] in
theorem nativeTensorFirst_augmented :
    type_of% (ResolutionProducts.natCubic_endExt_eq (k := k)
      (ExternalTensor.projectiveResolution k R S (nativeResolution k R M) (nativeResolution k S N))
      (ExternalTensor.firstComparison k R S (nativeResolution k R M) (nativeResolution k S N)
        (nativeCubicMap k R M p))
      (ExternalTensor.firstComparison_comm k R S (nativeResolution k R M) (nativeResolution k S N)
        (nativeCubicMap k R M p) (nativeCubicMap_comm k R M p hp))) :=
  ResolutionProducts.natCubic_endExt_eq (k := k)
    (ExternalTensor.projectiveResolution k R S (nativeResolution k R M) (nativeResolution k S N))
    (ExternalTensor.firstComparison k R S (nativeResolution k R M) (nativeResolution k S N)
      (nativeCubicMap k R M p))
    (ExternalTensor.firstComparison_comm k R S (nativeResolution k R M) (nativeResolution k S N)
      (nativeCubicMap k R M p) (nativeCubicMap_comm k R M p hp))

omit [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)] in
theorem nativeTensorSecond_augmented :
    type_of% (ResolutionProducts.natCubic_endExt_eq (k := k)
      (ExternalTensor.projectiveResolution k R S (nativeResolution k R M) (nativeResolution k S N))
      (ExternalTensor.secondComparison k R S (nativeResolution k R M) (nativeResolution k S N)
        (nativeCubicMap k S N r))
      (ExternalTensor.secondComparison_comm k R S (nativeResolution k R M) (nativeResolution k S N)
        (nativeCubicMap k S N r) (nativeCubicMap_comm k S N r hr))) :=
  ResolutionProducts.natCubic_endExt_eq (k := k)
    (ExternalTensor.projectiveResolution k R S (nativeResolution k R M) (nativeResolution k S N))
    (ExternalTensor.secondComparison k R S (nativeResolution k R M) (nativeResolution k S N)
      (nativeCubicMap k S N r))
    (ExternalTensor.secondComparison_comm k R S (nativeResolution k R M) (nativeResolution k S N)
      (nativeCubicMap k S N r) (nativeCubicMap_comm k S N r hr))

end ArExplicit.ModuleBar

end

end OAI
