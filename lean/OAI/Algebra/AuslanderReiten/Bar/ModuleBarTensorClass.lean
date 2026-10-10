import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorExt

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
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
  [HasDerivedCategory (ModuleCat.{u} (R ⊗[k] S))]
variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)
variable (r : AbsoluteBar.Cochain3 k S) (hr : AbsoluteBar.IsCocycle3 k S r)

omit [HasDerivedCategory (ModuleCat.{u} S)] in
theorem tensorFirst_action_of_class (a : Ext (ModuleCat.of R M) (ModuleCat.of R M) 3)
    (ha : extClass3 k R M p hp = a) (n : ℕ)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n) :
    tensorKunneth k R S M N (n+3) ((tensorFirst k R S M N p hp).comp x (by omega)) =
      ExternalTensor.coefficientFirst k R S (ModuleCat.of R M) (ModuleCat.of R M)
        (ModuleCat.of S N) (ModuleCat.of S N) a n (tensorKunneth k R S M N n x) := by
  rw [tensorFirst_action, ha]

omit [HasDerivedCategory (ModuleCat.{u} R)] in
theorem tensorSecond_action_of_class (a : Ext (ModuleCat.of S N) (ModuleCat.of S N) 3)
    (ha : extClass3 k S N r hr = a) (n : ℕ)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n) :
    tensorKunneth k R S M N (n+3) ((tensorSecond k R S M N r hr).comp x (by omega)) =
      ExternalTensor.coefficientSecond k R S (ModuleCat.of R M) (ModuleCat.of R M)
        (ModuleCat.of S N) (ModuleCat.of S N) a n (tensorKunneth k R S M N n x) := by
  rw [tensorSecond_action, ha]

omit [HasDerivedCategory (ModuleCat.{u} S)] in
theorem nativeTensorFirst_action_of_class (a : Ext (ModuleCat.of R M) (ModuleCat.of R M) 3)
    (ha : extClass3 k R M p hp = a) (n : ℕ)
    (x : Ext (ExternalTensor.canonicalTensorObject k R S M N)
      (ExternalTensor.canonicalTensorObject k R S M N) n) :
    nativeTensorKunneth k R S M N (n+3) ((nativeTensorFirst k R S M N p hp).comp x (by omega)) =
      ExternalTensor.coefficientFirst k R S (ModuleCat.of R M) (ModuleCat.of R M)
        (ModuleCat.of S N) (ModuleCat.of S N) a n (nativeTensorKunneth k R S M N n x) := by
  rw [nativeTensorFirst_action, ha]

omit [HasDerivedCategory (ModuleCat.{u} R)] in
theorem nativeTensorSecond_action_of_class (a : Ext (ModuleCat.of S N) (ModuleCat.of S N) 3)
    (ha : extClass3 k S N r hr = a) (n : ℕ)
    (x : Ext (ExternalTensor.canonicalTensorObject k R S M N)
      (ExternalTensor.canonicalTensorObject k R S M N) n) :
    nativeTensorKunneth k R S M N (n+3) ((nativeTensorSecond k R S M N r hr).comp x (by omega)) =
      ExternalTensor.coefficientSecond k R S (ModuleCat.of R M) (ModuleCat.of R M)
        (ModuleCat.of S N) (ModuleCat.of S N) a n (nativeTensorKunneth k R S M N n x) := by
  rw [nativeTensorSecond_action, ha]
end ArExplicit.ModuleBar

end

end OAI
