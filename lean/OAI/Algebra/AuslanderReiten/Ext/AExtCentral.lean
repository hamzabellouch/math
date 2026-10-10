import OAI.Algebra.AuslanderReiten.Ext.AExtActions
import OAI.Algebra.AuslanderReiten.Ext.TTensorGeneration
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTensorCentral
import OAI.Algebra.AuslanderReiten.Homology.AEndHomScalar

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

theorem aExt_cubic_central (n : ℕ) (x : ASelfExt q (3*n)) :
    type_of% (ModuleBar.tensor_cubic_central k T T (Simple q) (Simple q)
      (CocycleData.p q) (CocycleData.p_isCocycle3 q)
      (CocycleData.p q) (CocycleData.p_isCocycle3 q)
      (tExplicitP q) (aFactorExtClass q) (tExplicitP q) (aFactorExtClass q)
      (tTensor_generation q hq hq1 h) (aEndHom_scalar q hq1) n x) :=
  ModuleBar.tensor_cubic_central k T T (Simple q) (Simple q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q)
    (tExplicitP q) (aFactorExtClass q) (tExplicitP q) (aFactorExtClass q)
    (tTensor_generation q hq hq1 h) (aEndHom_scalar q hq1) n x

end ArExplicit.Resolution

end

end OAI
