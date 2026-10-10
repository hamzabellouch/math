import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonStrandReconstruction

namespace OAI

open CategoryTheory Classical Set
namespace SimpleAmenable.PolygonObject

structure Labelled (a n : ℕ) where
  polygon : PolygonObject a
  label : Fin polygon.tracks → Fin n → CutRing × CutRing
  reduced : ∀ j i, orbitRepresentative (label j i) = label j i

namespace Labelled
variable {a n : ℕ}
structure Hom (U V : Labelled a n) where
  arrow : U.polygon ⟶ V.polygon
  positional : Positional arrow
  labelled : ∀ x, V.label (arrow.toEquiv x).val.1 = U.label x.val.1

@[ext] theorem Hom.ext {U V : Labelled a n} (f g : Hom U V) (h : f.arrow = g.arrow) : f=g := by
  cases f; cases g; cases h; rfl

noncomputable instance : Category (Labelled a n) where
  Hom := Hom
  id object := ⟨𝟙 object.polygon, (fun _ => rfl), fun _ => rfl⟩
  comp f g := ⟨f.arrow ≫ g.arrow, positional_comp f.positional g.positional,
    fun point => (g.labelled (f.arrow.toEquiv point)).trans (f.labelled point)⟩
  id_comp _ := Hom.ext _ _ (Category.id_comp _)
  comp_id _ := Hom.ext _ _ (Category.comp_id _)
  assoc _ _ _ := Hom.ext _ _ (Category.assoc _ _ _)

noncomputable instance {U V : Labelled a n} (f : U ⟶ V) : IsIso f := by
  refine ⟨⟨⟨inv f.arrow,positional_inv f.positional,?_⟩,?_,?_⟩⟩
  · intro x
    obtain ⟨y,rfl⟩ := f.arrow.toEquiv.surjective x
    simpa only [inv_arrow_apply,Equiv.symm_apply_apply] using (f.labelled y).symm
  · apply Hom.ext; exact IsIso.hom_inv_id _
  · apply Hom.ext; exact IsIso.inv_hom_id _

noncomputable instance : Groupoid (Labelled a n) := Groupoid.ofIsIso (fun _ => inferInstance)

noncomputable abbrev string (U : Labelled a n) : StringGroupoid a n :=
  ⟨incrementString U.polygon U.label⟩
noncomputable abbrev initial (U : Labelled a n) := incrementInitial U.polygon U.label

noncomputable def initialArrow {U V : Labelled a n} (f : U ⟶ V) :
    (string U).obj.obj 0 ⟶ (string V).obj.obj 0 :=
  inv (initial U) ≫ f.arrow ≫ initial V

theorem initialArrow_positional {U V : Labelled a n} (f : U ⟶ V) :
    Positional (initialArrow f) :=
  positional_comp (positional_inv (incrementInitial_positional _ _))
    (positional_comp f.positional (incrementInitial_positional _ _))

theorem initialArrow_labelled {U V : Labelled a n} (f : U ⟶ V)
    (x : ((string U).obj.obj 0).Point) :
    increments (string V).obj ((initialArrow f).toEquiv x) = increments (string U).obj x := by
  obtain ⟨y,rfl⟩ := (initial U).toEquiv.surjective x
  simp only [initialArrow,arrow_comp_apply,inv_arrow_apply,Equiv.symm_apply_apply]
  rw [incrementString_spec_reduced _ _ V.reduced,incrementString_spec_reduced _ _ U.reduced]
  exact f.labelled y

noncomputable def ladder {U V : Labelled a n} (f : U ⟶ V) : string U ⟶ string V :=
  ⟨extendLadder (initialArrow f),extendLadder_positional_of_increments _
    (initialArrow_positional f) (initialArrow_labelled f)⟩

@[simp] theorem ladder_zero {U V : Labelled a n} (f : U ⟶ V) :
    (ladder f).hom.app 0 = initialArrow f := extendLadder_zero _

noncomputable def toStrings : Labelled a n ⥤ StringGroupoid a n where
  obj := string
  map := ladder
  map_id U := by
    apply WideSubcategory.hom_ext
    apply ladder_ext
    change (ladder (𝟙 U)).hom.app 0 = 𝟙 _
    rw [ladder_zero]
    change inv (initial U) ≫ (𝟙 _) ≫ initial U = 𝟙 _
    simp
  map_comp f g := by
    apply WideSubcategory.hom_ext
    apply ladder_ext
    change (ladder (f ≫ g)).hom.app 0 = (ladder f).hom.app 0 ≫ (ladder g).hom.app 0
    rw [ladder_zero,ladder_zero,ladder_zero]
    change inv _ ≫ (f.arrow ≫ g.arrow) ≫ _ = initialArrow f ≫ initialArrow g
    simp [initialArrow,Category.assoc]

noncomputable def fromLadder {U V : Labelled a n} (f : string U ⟶ string V) : U ⟶ V where
  arrow := initial U ≫ f.hom.app 0 ≫ inv (initial V)
  positional := positional_comp (incrementInitial_positional _ _)
    (positional_comp (f.property 0) (positional_inv (incrementInitial_positional _ _)))
  labelled x := by
    have h := ladder_preserves_increments f ((initial U).toEquiv x)
    rw [incrementString_spec_reduced _ _ U.reduced] at h
    have hv := incrementString_spec_reduced V.polygon V.label V.reduced
      ((initial V).toEquiv.symm ((f.hom.app 0).toEquiv ((initial U).toEquiv x)))
    simp only [Equiv.apply_symm_apply] at hv
    simpa only [arrow_comp_apply,inv_arrow_apply] using hv.symm.trans h

noncomputable instance : toStrings (a:=a) (n:=n) |>.Full where
  map_surjective f := ⟨fromLadder f,by
    apply WideSubcategory.hom_ext
    apply ladder_ext
    change (ladder (fromLadder f)).hom.app 0 = f.hom.app 0
    rw [ladder_zero]
    simp [initialArrow,fromLadder,Category.assoc]⟩

instance : toStrings (a:=a) (n:=n) |>.Faithful where
  map_injective {U V} f g h := by
    have h0 := congrArg (fun h : string U ⟶ string V => h.hom.app 0) h
    change (ladder f).hom.app 0 = (ladder g).hom.app 0 at h0
    rw [ladder_zero,ladder_zero] at h0
    apply Hom.ext
    simpa [initialArrow,Category.assoc] using congrArg (fun h => initial U ≫ h ≫ inv (initial V)) h0

theorem increments_reduced (F : RawString a n) (x : (F.obj 0).Point) (i : Fin n) :
    orbitRepresentative (increments F x i) = increments F x i := by
  simp only [increments,representative_sub,trajectoryShift,pointShift_reduced]

abbrev Support (F : RawString a n) := Set.range (increments F)
noncomputable instance (F : RawString a n) : Fintype (Support F) :=
  (increments_finite_range F).fintype
noncomputable def supportLabel (F : RawString a n) (x : (F.obj 0).Point) : Support F :=
  ⟨increments F x,⟨x,rfl⟩⟩
theorem supportLabel_polygon (F : RawString a n) (j : Fin (F.obj 0).tracks) (k : Support F) :
    {z | ∃hz : z∈((F.obj 0).cell j).val,supportLabel F ⟨(j,z),hz⟩=k}∈polygonAlgebra a := by
  simpa only [Subtype.ext_iff,supportLabel] using increments_fiber_polygon F j k.val

noncomputable def refine (F : RawString a n) : Labelled a n where
  polygon := refinement (F.obj 0) (supportLabel F) (supportLabel_polygon F)
  label j := ((Fintype.equivFin (Fin (F.obj 0).tracks × Support F)).symm j).2.val
  reduced j i := by
    obtain ⟨x,hx⟩ := ((Fintype.equivFin (Fin (F.obj 0).tracks × Support F)).symm j).2.property
    rw [←hx]
    exact increments_reduced F x i

noncomputable def drop (F : RawString a n) : (refine F).polygon ⟶ F.obj 0 :=
  refinementArrow (F.obj 0) (supportLabel F) (supportLabel_polygon F)

theorem drop_label (F : RawString a n) (x : (refine F).polygon.Point) :
    increments F ((drop F).toEquiv x) = (refine F).label x.val.1 :=
  congrArg Subtype.val (refinementArrow_label (F.obj 0) (supportLabel F) (supportLabel_polygon F) x)

noncomputable def refinementLadder (F : RawString a n) : string (refine F) ⟶ (⟨F⟩ : StringGroupoid a n) := by
  let h := inv (initial (refine F)) ≫ drop F
  refine (incrementLadderEquiv _ _).symm ⟨h,?_,?_⟩
  · exact positional_comp (positional_inv (incrementInitial_positional _ _))
      (refinementArrow_positional _ _ _)
  · intro x
    obtain ⟨y,rfl⟩ := (initial (refine F)).toEquiv.surjective x
    simp only [h,arrow_comp_apply,inv_arrow_apply,Equiv.symm_apply_apply]
    rw [incrementString_spec_reduced _ _ (refine F).reduced]
    exact drop_label F y
noncomputable instance : toStrings (a:=a) (n:=n) |>.EssSurj where
  mem_essImage F := by
    let e := asIso (refinementLadder F.obj)
    exact ⟨refine F.obj,⟨e⟩⟩

noncomputable instance : toStrings (a:=a) (n:=n) |>.IsEquivalence where

noncomputable def equivalence (a n : ℕ) : Labelled a n ≌ StringGroupoid a n :=
  toStrings.asEquivalence

end Labelled
end SimpleAmenable.PolygonObject

end OAI
