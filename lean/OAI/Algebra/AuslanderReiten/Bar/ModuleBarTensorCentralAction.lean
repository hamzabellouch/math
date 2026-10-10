import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorCentral

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
variable (hgen : ∀ n : ℕ, ∀ z : ExternalTensor.extCoefficients k R S
    (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) (3*n+3),
  ∃ u v : ExternalTensor.extCoefficients k R S
    (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) (3*n),
    z = ExternalTensor.coefficientFirst k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) a (3*n) u +
    ExternalTensor.coefficientSecond k R S
      (ModuleCat.of R M) (ModuleCat.of R M) (ModuleCat.of S N) (ModuleCat.of S N) b (3*n) v)
include ha hb hgen

theorem tensorFirst_action_right
    (hhom : ∀ f : ExternalTensor.moduleObject k R S M N ⟶ ExternalTensor.moduleObject k R S M N,
      ∃ c : k, ∀ z : ExternalTensor.moduleObject k R S M N,
        f.hom z = (algebraMap k (R ⊗[k] S) c) • z)
    (n : ℕ) (x : Ext (ExternalTensor.moduleObject k R S M N)
      (ExternalTensor.moduleObject k R S M N) (3*n)) :
    tensorKunneth k R S M N (3*n+3) (x.comp (tensorFirst k R S M N p hp) rfl) =
      ExternalTensor.coefficientFirst k R S (ModuleCat.of R M) (ModuleCat.of R M)
        (ModuleCat.of S N) (ModuleCat.of S N) a (3*n) (tensorKunneth k R S M N (3*n) x) := by
  rw [← (tensor_cubic_central k R S M N p hp r hr a ha b hb hgen hhom n x).1]
  exact tensorFirst_action_of_class k R S M N p hp a ha (3*n) x

theorem tensorSecond_action_right
    (hhom : ∀ f : ExternalTensor.moduleObject k R S M N ⟶ ExternalTensor.moduleObject k R S M N,
      ∃ c : k, ∀ z : ExternalTensor.moduleObject k R S M N,
        f.hom z = (algebraMap k (R ⊗[k] S) c) • z)
    (n : ℕ) (x : Ext (ExternalTensor.moduleObject k R S M N)
      (ExternalTensor.moduleObject k R S M N) (3*n)) :
    tensorKunneth k R S M N (3*n+3) (x.comp (tensorSecond k R S M N r hr) rfl) =
      ExternalTensor.coefficientSecond k R S (ModuleCat.of R M) (ModuleCat.of R M)
        (ModuleCat.of S N) (ModuleCat.of S N) b (3*n) (tensorKunneth k R S M N (3*n) x) := by
  rw [← (tensor_cubic_central k R S M N p hp r hr a ha b hb hgen hhom n x).2]
  exact tensorSecond_action_of_class k R S M N r hr b hb (3*n) x

end ArExplicit.ModuleBar

end

end OAI
