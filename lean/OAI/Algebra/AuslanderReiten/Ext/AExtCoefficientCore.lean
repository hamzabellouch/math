import OAI.Algebra.AuslanderReiten.Ext.AExtActions
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
  [HasDerivedCategory (ModuleCat.{u} R)]
  [HasDerivedCategory (ModuleCat.{u} (R ⊗[k] S))]
variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)
private theorem tensorFirst_action_map (a : Ext (ModuleCat.of R M) (ModuleCat.of R M) 3)
    (ha : extClass3 k R M p hp = a) (n : ℕ) {W : Sort v}
    (C : ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M)
      (ModuleCat.of S N) (ModuleCat.of S N) (n+3) → W)
    (D : ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M)
      (ModuleCat.of S N) (ModuleCat.of S N) n → W)
    (hC : ∀ z, C (ExternalTensor.coefficientFirst k R S (ModuleCat.of R M) (ModuleCat.of R M)
      (ModuleCat.of S N) (ModuleCat.of S N) a n z) = D z)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n) :
    C (tensorKunneth k R S M N (n+3) ((tensorFirst k R S M N p hp).comp x (by omega))) =
      D (tensorKunneth k R S M N n x) :=
  (congrArg C (tensorFirst_action_of_class k R S M N p hp a ha n x)).trans (hC _)

variable [HasDerivedCategory (ModuleCat.{u} S)]
variable (r : AbsoluteBar.Cochain3 k S) (hr : AbsoluteBar.IsCocycle3 k S r)
omit [HasDerivedCategory (ModuleCat.{u} R)] in
private theorem tensorSecond_action_map (a : Ext (ModuleCat.of S N) (ModuleCat.of S N) 3)
    (ha : extClass3 k S N r hr = a) (n : ℕ) {W : Sort v}
    (C : ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M)
      (ModuleCat.of S N) (ModuleCat.of S N) (n+3) → W)
    (D : ExternalTensor.extCoefficients k R S (ModuleCat.of R M) (ModuleCat.of R M)
      (ModuleCat.of S N) (ModuleCat.of S N) n → W)
    (hC : ∀ z, C (ExternalTensor.coefficientSecond k R S (ModuleCat.of R M) (ModuleCat.of R M)
      (ModuleCat.of S N) (ModuleCat.of S N) a n z) = D z)
    (x : Ext (ExternalTensor.moduleObject k R S M N) (ExternalTensor.moduleObject k R S M N) n) :
    C (tensorKunneth k R S M N (n+3) ((tensorSecond k R S M N r hr).comp x (by omega))) =
      D (tensorKunneth k R S M N n x) :=
  (congrArg C (tensorSecond_action_of_class k R S M N r hr a ha n x)).trans (hC _)
end ArExplicit.ModuleBar
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q ⊗[k] ArExplicit.T k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : NoPositivePowerOne q)
include hq hq1 h
local notation "T" => ArExplicit.T k q
private abbrev firstCoefficientProof (n : ℕ) (x : ASelfExt q (3*n)) :=
  ModuleBar.tensorFirst_action_map k T T (Simple q) (Simple q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q) (tExplicitP q) (aFactorExtClass q) (3*n)
    (tTensorCoefficientEquiv q hq hq1 h (n+1))
    (fun z => BinaryKoszul.mulX k n (tTensorCoefficientEquiv q hq hq1 h n z))
    (tTensorCoefficient_first q hq hq1 h n) x

theorem aExtCoefficient_first (n : ℕ) (x : ASelfExt q (3*n)) :
    type_of% (firstCoefficientProof q hq hq1 h n x) :=
  firstCoefficientProof q hq hq1 h n x

private abbrev secondCoefficientProof (n : ℕ) (x : ASelfExt q (3*n)) :=
  ModuleBar.tensorSecond_action_map k T T (Simple q) (Simple q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q) (tExplicitP q) (aFactorExtClass q) (3*n)
    (tTensorCoefficientEquiv q hq hq1 h (n+1))
    (fun z => BinaryKoszul.mulY k n (tTensorCoefficientEquiv q hq hq1 h n z))
    (tTensorCoefficient_second q hq hq1 h n) x

theorem aExtCoefficient_second (n : ℕ) (x : ASelfExt q (3*n)) :
    type_of% (secondCoefficientProof q hq hq1 h n x) :=
  secondCoefficientProof q hq hq1 h n x
end ArExplicit.Resolution

end

end OAI
