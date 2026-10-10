import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorExt
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorCubicProducts

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R S M N : Type u) [Field k] [CharP k 2]
  [Ring R] [Algebra k R] [Module.Finite k R] [Ring S] [Algebra k S] [Module.Finite k S]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [Module.Finite k M]
  [AddCommGroup N] [Module S N] [Module k N] [IsScalarTower k S N] [Module.Finite k N]
variable [HasDerivedCategory (ModuleCat.{u} (R ⊗[k] S))]
variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)
variable (r : AbsoluteBar.Cochain3 k S) (hr : AbsoluteBar.IsCocycle3 k S r)

theorem nativeTensorCubics_commute :
    (nativeTensorFirst k R S M N p hp).comp (nativeTensorSecond k R S M N r hr) rfl =
      (nativeTensorSecond k R S M N r hr).comp (nativeTensorFirst k R S M N p hp) rfl :=
  ExternalTensor.cubicExt_commute k R S (nativeResolution k R M) (nativeResolution k S N)
    (nativeCubicMap k R M p) (nativeCubicMap k S N r)
    (nativeCubicMap_comm k R M p hp) (nativeCubicMap_comm k S N r hr)

theorem tensorCubics_commute :
    (tensorFirst k R S M N p hp).comp (tensorSecond k R S M N r hr) rfl =
      (tensorSecond k R S M N r hr).comp (tensorFirst k R S M N p hp) rfl := by
  unfold tensorFirst tensorSecond
  rw [← ExternalTensor.selfExtScalarEquiv_symm_comp,
    ← ExternalTensor.selfExtScalarEquiv_symm_comp]
  exact congrArg (ExternalTensor.selfExtScalarEquiv k R S M N 6).symm
    (nativeTensorCubics_commute k R S M N p hp r hr)

end ArExplicit.ModuleBar

end

end OAI
