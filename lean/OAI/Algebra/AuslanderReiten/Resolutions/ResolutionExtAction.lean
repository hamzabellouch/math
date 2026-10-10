import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionProductCompatibility

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

def conjugateTo {X X' Y Y' : DerivedCategory C} (e : X ≅ X') (t : Y ≅ Y')
    {n : ℤ} (f : ShiftedHom X Y n) : ShiftedHom X' Y' n :=
  e.inv ≫ f ≫ (CategoryTheory.shiftFunctor (DerivedCategory C) n).map t.hom

theorem conjugateTo_comp {X X' Y Y' Z Z' : DerivedCategory C}
    (e : X ≅ X') (t : Y ≅ Y') (w : Z ≅ Z')
    {n m r : ℤ} (f : ShiftedHom X Y n) (g : ShiftedHom Y Z m) (h : m+n=r) :
    conjugateTo e w (f.comp g h) = (conjugateTo e t f).comp (conjugateTo t w g) h := by
  simp only [conjugateTo, ShiftedHom.comp, Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((CategoryTheory.shiftFunctor (DerivedCategory C) n).map t.hom),
    ← Functor.map_comp, t.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact congrArg (fun z => e.inv ≫ f ≫
    (CategoryTheory.shiftFunctor (DerivedCategory C) n).map g ≫ z)
      ((CategoryTheory.shiftFunctorAdd' (DerivedCategory C) m n r h).inv.naturality w.hom).symm

variable [HasExt.{v} C]

def extOfCocycle {X Y : C} (P : ProjectiveResolution X) {n : ℕ}
    (y : Cocycle P.cochainComplex ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ)) :
    Ext X Y n := P.extEquivCohomologyClass.symm (CohomologyClass.mk y)

theorem extOfCocycle_hom {X Y : C} (P : ProjectiveResolution X) {n : ℕ}
    (y : Cocycle P.cochainComplex ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ)) :
    (extOfCocycle P y).hom = conjugateTo (resolutionIso P)
      ((DerivedCategory.singleFunctorIsoCompQ C 0).symm.app Y)
      (ShiftedHom.map (Cocycle.equivHomShift.symm y) DerivedCategory.Q) := by
  rw [extOfCocycle, P.extEquivCohomologyClass_symm_mk_hom]
  simp only [conjugateTo, resolutionIso, Iso.trans_inv, asIso_inv,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Category.assoc]
  rfl

theorem endExt_comp_extOfCocycle {X Y : C} (P : ProjectiveResolution X) {n m r : ℕ}
    (x : Cocycle P.cochainComplex P.cochainComplex (n : ℤ))
    (y : Cocycle P.cochainComplex ((CochainComplex.singleFunctor C 0).obj Y) (m : ℤ))
    (z : Cocycle P.cochainComplex ((CochainComplex.singleFunctor C 0).obj Y) (r : ℤ))
    (h : n+m=r) (hz : z.val=x.val.comp y.val (by omega)) :
    (endExt P x).comp (extOfCocycle P y) h = extOfCocycle P z := by
  apply Ext.homEquiv.injective
  change ((endExt P x).comp (extOfCocycle P y) h).hom = (extOfCocycle P z).hom
  rw [Ext.comp_hom, endExt_hom, extOfCocycle_hom, extOfCocycle_hom,
    cocycleHom_comp (by omega) x y z hz, ShiftedHom.map_comp]
  exact (conjugateTo_comp (resolutionIso P) (resolutionIso P)
    ((DerivedCategory.singleFunctorIsoCompQ C 0).symm.app Y) _ _ _).symm

end ArExplicit.ResolutionProducts

end

end OAI
