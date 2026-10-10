import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorClass
import OAI.Algebra.AuslanderReiten.Ext.ExtGenerationTransfer

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
variable [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
  [HasDerivedCategory (ModuleCat.{u} (R ⊗[k] S))]
variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)
variable (r : AbsoluteBar.Cochain3 k S) (hr : AbsoluteBar.IsCocycle3 k S r)
variable (a : Ext (ModuleCat.of R M) (ModuleCat.of R M) 3)
  (ha : extClass3 k R M p hp = a)
  (b : Ext (ModuleCat.of S N) (ModuleCat.of S N) 3)
  (hb : extClass3 k S N r hr = b)
include ha hb

theorem tensor_generation (n : ℕ)
    (hgen : ∀ z : ExternalTensor.extCoefficients k R S
        (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) (n+3),
      ∃ u v : ExternalTensor.extCoefficients k R S
        (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) n,
        z = ExternalTensor.coefficientFirst k R S
          (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) a n u +
        ExternalTensor.coefficientSecond k R S
          (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) b n v)
    (x : Ext (ExternalTensor.moduleObject k R S M N)
      (ExternalTensor.moduleObject k R S M N) (n+3)) :
    ∃ u v : Ext (ExternalTensor.moduleObject k R S M N)
        (ExternalTensor.moduleObject k R S M N) n,
      x = (tensorFirst k R S M N p hp).comp u (by omega) +
        (tensorSecond k R S M N r hr).comp v (by omega) :=
  ResolutionProducts.generationOfAddEquiv
    (tensorFirst k R S M N p hp) (tensorSecond k R S M N r hr)
    (tensorKunneth k R S M N n).toAddEquiv
    (tensorKunneth k R S M N (n+3)).toAddEquiv
    (ExternalTensor.coefficientFirst k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) a n)
    (ExternalTensor.coefficientSecond k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) b n)
    (tensorFirst_action_of_class k R S M N p hp a ha n)
    (tensorSecond_action_of_class k R S M N r hr b hb n) hgen x

end ArExplicit.ModuleBar

end

end OAI
