import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.GroupNerveCoordinates
import OAI.GroupTheory.SimpleAmenable.Simplicial.PiFiber

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite
namespace GroupoidComponentHomology
open FreeChains ComponentTranslation SimpleAmenable

variable {C:Type} [Groupoid.{0} C]
noncomputable def inclusion (U:C) : SingleObj (Aut U) ⥤ C :=
  SingleObj.functor (Aut.toEnd U)
@[simp] lemma inclusion_obj (U:C) (x:SingleObj (Aut U)) : (inclusion U).obj x=U := rfl
@[simp] lemma inclusion_map (U:C) {x y:SingleObj (Aut U)} (f:x⟶y) :
    (inclusion U).map f=f.hom := rfl
instance inclusion_faithful (U:C) : (inclusion U).Faithful where
  map_injective h := Iso.ext h
noncomputable instance inclusion_full (U:C) : (inclusion U).Full where
  map_surjective f := ⟨(Groupoid.isoEquivHom U U).symm f,rfl⟩
noncomputable def fiberInclusion {p:Skeleton C} (U:Fiber p) : SingleObj (Aut U.obj) ⥤ Fiber p :=
  (property p).lift (inclusion U.obj) (fun _=>U.property)
instance fiberInclusion_faithful {p:Skeleton C} (U:Fiber p) : (fiberInclusion U).Faithful where
  map_injective h := Iso.ext (congrArg (fun f : (fiberInclusion U).obj _ ⟶ (fiberInclusion U).obj _ => f.hom) h)
noncomputable instance fiberInclusion_full {p:Skeleton C} (U:Fiber p) : (fiberInclusion U).Full where
  map_surjective f := ⟨(Groupoid.isoEquivHom U.obj U.obj).symm f.hom,rfl⟩
instance fiberInclusion_essSurj {p:Skeleton C} (U:Fiber p) : (fiberInclusion U).EssSurj where
  mem_essImage V := ⟨SingleObj.star _,⟨fiberIso p U V⟩⟩
noncomputable instance fiberInclusion_isEquivalence {p:Skeleton C} (U:Fiber p) :
    (fiberInclusion U).IsEquivalence := ⟨inferInstance,inferInstance,inferInstance⟩
noncomputable def fiberIsoHomology {p:Skeleton C} (U:Fiber p) (q:ℕ) :
    groupHomology (Rep.trivial ℤ (Aut U.obj) ℤ) q ≅ (nerve (Fiber p)).homology Z q := by
  haveI := NerveHomotopy.homologyMap_isIso (fiberInclusion U) Z q
  exact (GroupNerveCoordinates.homologyIso (Aut U.obj) q).symm ≪≫
    asIso (SSet.homologyMap (nerveMap (fiberInclusion U)) Z q)
end GroupoidComponentHomology

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory
namespace TranslationFiltered

variable (P:Type) [CommMonoid P]
instance regular_filtered : IsFiltered (ActionCategory P P) where
  cocone_objs x y := ⟨(x.back*y.back:P),⟨y.back, by change y.back*x.back=x.back*y.back; exact mul_comm _ _⟩,⟨x.back,rfl⟩,trivial⟩
  cocone_maps {x y} f g := by
    refine ⟨(x.back*y.back:P),⟨x.back,rfl⟩,?_⟩
    apply Functor.Elements.Hom.ext
    change x.back*f.hom=x.back*g.hom
    have h:f.hom*x.back=g.hom*x.back:=f.map_val.trans g.map_val.symm
    simpa only [mul_comm] using h
  nonempty := inferInstance
abbrev Q := Algebra.GrothendieckGroup P
noncomputable instance completed_action : MulAction P (Q P) :=
  MulAction.compHom (Q P) Algebra.GrothendieckGroup.of
lemma common_target (x y:Q P) : ∃ r s:P,
    Algebra.GrothendieckGroup.of r*x=Algebra.GrothendieckGroup.of s*y := by
  let f:=Localization.monoidOf (⊤:Submonoid P)
  let t:=f.sec (x*y⁻¹)
  refine ⟨t.2.val,t.1,?_⟩
  calc
    _ = ((x*y⁻¹)*f t.2)*y := by change f t.2*x=_; simp [mul_assoc,mul_comm,mul_left_comm]
    _ = _ := congrArg (fun q:Q P => q*y) (f.sec_spec (x*y⁻¹))
noncomputable instance completed_filtered : IsFiltered (ActionCategory P (Q P)) where
  cocone_objs x y := by
    obtain ⟨r,s,h⟩:=common_target P x.back y.back
    exact ⟨(Algebra.GrothendieckGroup.of r*x.back:Q P),⟨r,rfl⟩,⟨s,h.symm⟩,trivial⟩
  cocone_maps {x y} f g := by
    have he : Algebra.GrothendieckGroup.of f.hom=Algebra.GrothendieckGroup.of g.hom := by
      apply mul_right_cancel (b:=x.back)
      exact f.map_val.trans g.map_val.symm
    obtain ⟨c,hc⟩ := (Localization.monoidOf (⊤:Submonoid P)).exists_of_eq he
    refine ⟨(Algebra.GrothendieckGroup.of c.val*y.back:Q P),⟨c.val,rfl⟩,?_⟩
    exact Functor.Elements.Hom.ext hc
  nonempty := inferInstance
end TranslationFiltered

end

end OAI
