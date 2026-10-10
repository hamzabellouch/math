import OAI.Algebra.AuslanderReiten.Ext.AExtActions
import OAI.Algebra.AuslanderReiten.Ext.TTensorGeneration
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorGeneration

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

theorem aExt_generation (n : ℕ) (x : ASelfExt q (3*(n+1))) :
    type_of% (ModuleBar.tensor_generation k T T (Simple q) (Simple q)
      (CocycleData.p q) (CocycleData.p_isCocycle3 q)
      (CocycleData.p q) (CocycleData.p_isCocycle3 q)
      (tExplicitP q) (aFactorExtClass q) (tExplicitP q) (aFactorExtClass q)
      (3*n) (tTensor_generation q hq hq1 h n) x) :=
  ModuleBar.tensor_generation k T T (Simple q) (Simple q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (tExplicitP q) (aFactorExtClass q) (tExplicitP q) (aFactorExtClass q)
    (3*n) (tTensor_generation q hq hq1 h n) x

end ArExplicit.Resolution

end

end OAI
