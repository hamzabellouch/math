import OAI.Algebra.AuslanderReiten.HomComplex.FullHomProducts
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

def conjugate {X Y : DerivedCategory C} (e : X ≅ Y) {n : ℤ}
    (f : ShiftedHom X X n) : ShiftedHom Y Y n :=
  e.inv ≫ f ≫ (CategoryTheory.shiftFunctor (DerivedCategory C) n).map e.hom

theorem conjugate_comp {X Y : DerivedCategory C} (e : X ≅ Y) {n m : ℤ}
    (f : ShiftedHom X X n) (g : ShiftedHom X X m) :
    conjugate e (f.comp g (add_comm m n)) =
      (conjugate e f).comp (conjugate e g) (add_comm m n) := by
  simp only [conjugate, ShiftedHom.comp, Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((CategoryTheory.shiftFunctor (DerivedCategory C) n).map e.hom),
    ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact congrArg (fun h => e.inv ≫ f ≫
    (CategoryTheory.shiftFunctor (DerivedCategory C) n).map g ≫ h)
      ((CategoryTheory.shiftFunctorAdd' (DerivedCategory C) m n (n+m) (add_comm m n)).inv.naturality e.hom).symm

def resolutionIso {X : C} (P : ProjectiveResolution X) :
    DerivedCategory.Q.obj P.cochainComplex ≅ (DerivedCategory.singleFunctor C 0).obj X :=
  asIso (DerivedCategory.Q.map P.π') ≪≫ (DerivedCategory.singleFunctorIsoCompQ C 0).symm.app X

variable [HasExt.{v} C]

def endExt {X : C} (P : ProjectiveResolution X) {n : ℕ}
    (x : Cocycle P.cochainComplex P.cochainComplex (n : ℤ)) : Ext X X n :=
  Ext.homEquiv.symm (conjugate (resolutionIso P)
    (ShiftedHom.map (Cocycle.equivHomShift.symm x) DerivedCategory.Q))

@[simp] theorem endExt_hom {X : C} (P : ProjectiveResolution X) {n : ℕ}
    (x : Cocycle P.cochainComplex P.cochainComplex (n : ℤ)) :
    (endExt P x).hom = conjugate (resolutionIso P)
      (ShiftedHom.map (Cocycle.equivHomShift.symm x) DerivedCategory.Q) :=
  Equiv.apply_symm_apply _ _

end ArExplicit.ResolutionProducts

end

end OAI
