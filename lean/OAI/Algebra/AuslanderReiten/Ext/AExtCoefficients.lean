import OAI.Algebra.AuslanderReiten.Ext.AExtRightActions
import OAI.Algebra.AuslanderReiten.Ext.AExtCoefficientCore
import OAI.Algebra.AuslanderReiten.Ext.TTensorActions

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u v
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

private theorem tensorFirst_action_right_map
    (hhom : ∀ f : ExternalTensor.moduleObject k R S M N ⟶ ExternalTensor.moduleObject k R S M N,
      ∃ c : k, ∀ z : ExternalTensor.moduleObject k R S M N,
        f.hom z = (algebraMap k (R ⊗[k] S) c) • z)
    (n : ℕ) {W : Sort v}
    (C : ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M)
      (ModuleCat.of S N) (ModuleCat.of S N) (3*n+3) → W)
    (D : ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M)
      (ModuleCat.of S N) (ModuleCat.of S N) (3*n) → W)
    (hC : ∀ z, C (ExternalTensor.coefficientFirst k R S (ModuleCat.of R M) (ModuleCat.of R M)
      (ModuleCat.of S N) (ModuleCat.of S N) a (3*n) z) = D z)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) (3*n)) :
    C (tensorKunneth k R S M N (3*n+3) (x.comp (tensorFirst k R S M N p hp) rfl)) =
      D (tensorKunneth k R S M N (3*n) x) :=
  (congrArg C (tensorFirst_action_right k R S M N p hp r hr a ha b hb hgen hhom n x)).trans (hC _)

private theorem tensorSecond_action_right_map
    (hhom : ∀ f : ExternalTensor.moduleObject k R S M N ⟶ ExternalTensor.moduleObject k R S M N,
      ∃ c : k, ∀ z : ExternalTensor.moduleObject k R S M N,
        f.hom z = (algebraMap k (R ⊗[k] S) c) • z)
    (n : ℕ) {W : Sort v}
    (C : ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M)
      (ModuleCat.of S N) (ModuleCat.of S N) (3*n+3) → W)
    (D : ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M)
      (ModuleCat.of S N) (ModuleCat.of S N) (3*n) → W)
    (hC : ∀ z, C (ExternalTensor.coefficientSecond k R S (ModuleCat.of R M) (ModuleCat.of R M)
      (ModuleCat.of S N) (ModuleCat.of S N) b (3*n) z) = D z)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) (3*n)) :
    C (tensorKunneth k R S M N (3*n+3) (x.comp (tensorSecond k R S M N r hr) rfl)) =
      D (tensorKunneth k R S M N (3*n) x) :=
  (congrArg C (tensorSecond_action_right k R S M N p hp r hr a ha b hb hgen hhom n x)).trans (hC _)

end ArExplicit.ModuleBar
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q ⊗[k] ArExplicit.T k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : NoPositivePowerOne q)
include hq hq1 h

local notation "T" => ArExplicit.T k q

private abbrev firstCoefficientRightProof (n : ℕ) (x : ASelfExt q (3*n)) :=
  ModuleBar.tensorFirst_action_right_map k T T (Simple q) (Simple q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (tExplicitP q) (aFactorExtClass q) (tExplicitP q) (aFactorExtClass q)
    (tTensor_generation q hq hq1 h) (aEndHom_scalar q hq1) n
    (tTensorCoefficientEquiv q hq hq1 h (n+1))
    (fun z => BinaryKoszul.mulX k n (tTensorCoefficientEquiv q hq hq1 h n z))
    (tTensorCoefficient_first q hq hq1 h n) x

theorem aExtCoefficient_first_right (n : ℕ) (x : ASelfExt q (3*n)) :
    type_of% (firstCoefficientRightProof q hq hq1 h n x) :=
  firstCoefficientRightProof q hq hq1 h n x

private abbrev secondCoefficientRightProof (n : ℕ) (x : ASelfExt q (3*n)) :=
  ModuleBar.tensorSecond_action_right_map k T T (Simple q) (Simple q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (tExplicitP q) (aFactorExtClass q) (tExplicitP q) (aFactorExtClass q)
    (tTensor_generation q hq hq1 h) (aEndHom_scalar q hq1) n
    (tTensorCoefficientEquiv q hq hq1 h (n+1))
    (fun z => BinaryKoszul.mulY k n (tTensorCoefficientEquiv q hq hq1 h n z))
    (tTensorCoefficient_second q hq hq1 h n) x

theorem aExtCoefficient_second_right (n : ℕ) (x : ASelfExt q (3*n)) :
    type_of% (secondCoefficientRightProof q hq hq1 h n x) :=
  secondCoefficientRightProof q hq hq1 h n x

end ArExplicit.Resolution

end

end OAI
