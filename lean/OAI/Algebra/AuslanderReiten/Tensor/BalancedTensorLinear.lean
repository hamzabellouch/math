import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorCategory
import Mathlib.CategoryTheory.Linear.LinearFunctor

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace ArExplicit.BalancedTensor
universe u
variable {k R S F : Type u} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module S F]
  [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
  [IsScalarTower k Rᵐᵒᵖ F] [IsScalarTower k S F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

instance functor_linear :
    (functor (k := k) (R := R) (S := S) (F := F)).Linear k where
  map_smul := by
    intro M N g a
    apply ModuleCat.hom_ext
    apply leftHom_ext
    intro f m
    change tmul (k := k) (R := R) f ((algebraMap k R a) • g.hom m) =
      (algebraMap k S a) • tmul (k := k) (R := R) f (g.hom m)
    rw [IsScalarTower.algebraMap_smul R a (g.hom m),
      IsScalarTower.algebraMap_smul S a (tmul (k := k) (R := R) f (g.hom m))]
    exact map_smul (mk (k := k) (R := R) f) a (g.hom m)

end ArExplicit.BalancedTensor

end

end OAI
