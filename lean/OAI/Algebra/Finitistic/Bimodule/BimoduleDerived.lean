import OAI.Algebra.Finitistic.Bimodule.BimoduleTensor
import Mathlib.CategoryTheory.Abelian.LeftDerived

namespace OAI
open CategoryTheory
noncomputable section

namespace DerivedBar.BimoduleTensor
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]

/-- The canonical field action on a left D-module. -/
@[instance_reducible] def scalarModule (V : ModuleCat.{u} D) : Module k V := Module.compHom V (algebraMap k D)

local instance (V : ModuleCat.{u} D) : Module k V := scalarModule k D V
local instance (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- Actual balanced tensor by the arbitrary bimodule X, as an additive endofunctor. -/
def tensorFunctor : ModuleCat.{u} D ⥤ ModuleCat.{u} D where
  obj V := ModuleCat.of D (tensor k D X V)
  map h := ModuleCat.ofHom (map k D X _ _ h.hom)
  map_id V := ModuleCat.hom_ext (map_id k D X V)
  map_comp h g := ModuleCat.hom_ext (map_comp k D X _ _ _ h.hom g.hom)

instance tensorFunctor_additive : (tensorFunctor k D X).Additive where
  map_add := by
    intro V W h g
    exact ModuleCat.hom_ext (map_add k D X _ _ h.hom g.hom)

/-- Tensor of X with the verified absolute bar projective resolution.
This construction applies the genuine balanced functor to every differential. -/
def resolvedTensor (N : ModuleCat.{u} D) : ChainComplex (ModuleCat.{u} D) ℕ :=
  ((tensorFunctor k D X).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (DerivedBar.projectiveResolution k D N).complex

/-- The explicit projective bar resolution computes actual derived tensor on modules,
via mathlib's left derived functor to the homotopy category.
Extension to bounded-above complexes and repeated totalization remains separate. -/
def barComputesDerivedTensor (N : ModuleCat.{u} D) :
    (tensorFunctor k D X).leftDerivedToHomotopyCategory.obj N ≅
      (HomotopyCategory.quotient (ModuleCat.{u} D) (ComplexShape.down ℕ)).obj
        (resolvedTensor k D X N) :=
  (DerivedBar.projectiveResolution k D N).isoLeftDerivedToHomotopyCategoryObj
    (tensorFunctor k D X)
end DerivedBar.BimoduleTensor

end

end OAI
