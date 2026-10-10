import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorExt
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorScalarIso

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

theorem tensorFirst_eq_of_conjugate
    (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) 3)
    (hx : selfExtIso (k := k) (ExternalTensor.canonicalTensorIso k R S M N).symm 3 x =
      nativeTensorFirst k R S M N p hp) :
    x = tensorFirst k R S M N p hp := by
  apply (ExternalTensor.selfExtScalarEquiv k R S M N 3).injective
  rw [tensorFirst, LinearEquiv.apply_symm_apply, ExternalTensor.selfExtScalarEquiv_eq_iso]
  exact hx

theorem tensorSecond_eq_of_conjugate
    (p : AbsoluteBar.Cochain3 k S) (hp : AbsoluteBar.IsCocycle3 k S p)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) 3)
    (hx : selfExtIso (k := k) (ExternalTensor.canonicalTensorIso k R S M N).symm 3 x =
      nativeTensorSecond k R S M N p hp) :
    x = tensorSecond k R S M N p hp := by
  apply (ExternalTensor.selfExtScalarEquiv k R S M N 3).injective
  rw [tensorSecond, LinearEquiv.apply_symm_apply, ExternalTensor.selfExtScalarEquiv_eq_iso]
  exact hx

end ArExplicit.ModuleBar

end

end OAI
