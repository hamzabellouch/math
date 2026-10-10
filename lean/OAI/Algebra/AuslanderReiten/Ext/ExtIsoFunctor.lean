import OAI.Algebra.AuslanderReiten.Ext.ExtIsoCongr
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace ArExplicit
universe u v w
variable {k : Type u} [CommRing k]
variable {C : Type v} [Category.{u} C] [Abelian C] [HasExt.{u} C] [Linear k C]
variable {D : Type w} [Category.{u} D] [Abelian D] [HasExt.{u} D] [Linear k D]
variable {X Y Z : C}

theorem selfExtIso_trans (e : X ≅ Y) (f : Y ≅ Z) (n : ℕ) (x : Ext X X n) :
    selfExtIso (k := k) f n (selfExtIso (k := k) e n x) =
      selfExtIso (k := k) (e ≪≫ f) n x := by
  simp [selfExtIso_apply]

theorem selfExtIso_symm_apply (e : X ≅ Y) (n : ℕ) (x : Ext Y Y n) :
    (selfExtIso (k := k) e n).symm x = selfExtIso (k := k) e.symm n x := by
  apply (selfExtIso (k := k) e n).injective
  simp [selfExtIso_apply]

theorem selfExtIso_eqToIso (h : X = Y) (n : ℕ) (x : Ext X X n) :
    selfExtIso (k := k) (eqToIso h) n x = h ▸ x := by
  subst h
  simp

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

theorem selfExtIso_mapExactFunctor (e : X ≅ Y) (n : ℕ) (x : Ext X X n) :
    (selfExtIso (k := k) e n x).mapExactFunctor F =
      selfExtIso (k := k) (F.mapIso e) n (x.mapExactFunctor F) := by
  simp only [selfExtIso_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Functor.mapIso_hom, Functor.mapIso_inv]

theorem selfExtIso_conjugated_functor
    (G : C ⥤ C) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : Y ≅ X) (E : Y ≅ G.obj Y) (n : ℕ) (x : Ext X X n) :
    selfExtIso (k := k) e n
      (selfExtIso (k := k) E.symm n
        ((selfExtIso (k := k) e.symm n x).mapExactFunctor G)) =
    selfExtIso (k := k) (e.symm ≪≫ E ≪≫ G.mapIso e).symm n
      (x.mapExactFunctor G) := by
  rw [selfExtIso_mapExactFunctor, selfExtIso_trans, selfExtIso_trans]
  have heq : G.mapIso e.symm ≪≫ E.symm ≪≫ e =
      (e.symm ≪≫ E ≪≫ G.mapIso e).symm := by
    apply Iso.ext
    simp
  rw [heq]

end ArExplicit

end

end OAI
