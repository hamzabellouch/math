import OAI.Algebra.AuslanderReiten.Triangular.TriangularComplete
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

namespace OAI

noncomputable section

namespace ArExplicit.TriangularInduction

open CategoryTheory
open CochainComplex CochainComplex.HomComplex

universe u

variable (k R F : Type u) [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

def eFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} (Triangular R F) where
  obj M := ModuleCat.of _ (TriangularE k R F M)
  map f := ModuleCat.ofHom (eMap f.hom)
  map_id M := by apply ModuleCat.hom_ext; exact eMap_id
  map_comp f g := by apply ModuleCat.hom_ext; exact eMap_comp f.hom g.hom

def jFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} (Triangular R F) where
  obj M := ModuleCat.of _ (TriangularJ k R F M)
  map f := ModuleCat.ofHom (jMap f.hom)
  map_id M := by apply ModuleCat.hom_ext; exact jMap_id
  map_comp f g := by apply ModuleCat.hom_ext; exact jMap_comp f.hom g.hom

instance : (eFunctor k R F).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply eHomEquiv.injective
    ext m
    rfl

instance : (jFunctor k R F).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply jHomEquiv.injective
    ext m
    rfl

instance : (eFunctor k R F).Faithful where
  map_injective := by
    intro M N f g h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact congrArg (fun a : (eFunctor k R F).obj M ⟶ (eFunctor k R F).obj N =>
      (a.hom ⟨m, 0⟩).top) h

instance : (jFunctor k R F).Faithful where
  map_injective := by
    intro M N f g h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact congrArg (fun a : (jFunctor k R F).obj M ⟶ (jFunctor k R F).obj N =>
      (a.hom ⟨0, m⟩).bottom) h

instance : (eFunctor k R F).Full where
  map_surjective := by
    intro M N g
    refine ⟨ModuleCat.ofHom (TriangularModule.topMap g.hom), ?_⟩
    apply ModuleCat.hom_ext
    exact eHom_topMap g.hom

instance : (jFunctor k R F).Full where
  map_surjective := by
    intro M N g
    refine ⟨ModuleCat.ofHom (TriangularModule.bottomMap g.hom), ?_⟩
    apply ModuleCat.hom_ext
    exact jHom_bottomMap g.hom

theorem eToJCochain_eq_zero (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (x : Cochain (((eFunctor k R F).mapHomologicalComplex _).obj P)
      (((jFunctor k R F).mapHomologicalComplex _).obj Q) n) : x = 0 := by
  apply Cochain.ext
  intro i j hij
  apply ModuleCat.hom_ext
  exact hom_E_J_eq_zero (x.v i j hij).hom

end ArExplicit.TriangularInduction

end

end OAI
