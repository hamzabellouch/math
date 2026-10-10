import OAI.Algebra.AuslanderReiten.Ext.AExtCentral
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorCentralAction

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q ⊗[k] ArExplicit.T k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : NoPositivePowerOne q)
local notation "T" => ArExplicit.T k q
include hq hq1 h

theorem aFirst_kunneth_right (n : ℕ) (x : ASelfExt q (3*n)) :
    type_of% (ModuleBar.tensorFirst_action_right k T T (Simple q) (Simple q)
      (CocycleData.p q) (CocycleData.p_isCocycle3 q)
      (CocycleData.p q) (CocycleData.p_isCocycle3 q)
      (tExplicitP q) (aFactorExtClass q) (tExplicitP q) (aFactorExtClass q)
      (tTensor_generation q hq hq1 h) (aEndHom_scalar q hq1) n x) :=
  ModuleBar.tensorFirst_action_right k T T (Simple q) (Simple q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (tExplicitP q) (aFactorExtClass q) (tExplicitP q) (aFactorExtClass q)
    (tTensor_generation q hq hq1 h) (aEndHom_scalar q hq1) n x

theorem aSecond_kunneth_right (n : ℕ) (x : ASelfExt q (3*n)) :
    type_of% (ModuleBar.tensorSecond_action_right k T T (Simple q) (Simple q)
      (CocycleData.p q) (CocycleData.p_isCocycle3 q)
      (CocycleData.p q) (CocycleData.p_isCocycle3 q)
      (tExplicitP q) (aFactorExtClass q) (tExplicitP q) (aFactorExtClass q)
      (tTensor_generation q hq hq1 h) (aEndHom_scalar q hq1) n x) :=
  ModuleBar.tensorSecond_action_right k T T (Simple q) (Simple q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (tExplicitP q) (aFactorExtClass q) (tExplicitP q) (aFactorExtClass q)
    (tTensor_generation q hq hq1 h) (aEndHom_scalar q hq1) n x

end ArExplicit.Resolution

end

end OAI
