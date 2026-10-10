import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ExactShapeHomology

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace ComponentStable
open FreeChains ComponentTranslation

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable abbrev H (q:ℕ) := SSet.homologyFunctor Z q
noncomputable abbrev object (q:ℕ) := colimit (homologyDiagram (C:=C) q)
noncomputable def inclusion (p:Skeleton C) (q:ℕ) :
    (nerve (Fiber p)).homology Z q ⟶ (nerve C).homology Z q :=
  SSet.homologyMap (nerveMap (property p).ι) Z q
noncomputable def unionCocone (q:ℕ) :
    Cocone (ComponentCoproduct.diagram C ⋙ H q) where
  pt := object (C:=C) q
  ι := Discrete.natTrans (fun p=>colimit.ι (homologyDiagram (C:=C) q) ((ActionCategory.objEquiv _ _) p.as))
noncomputable def toStable (q:ℕ) : (nerve C).homology Z q ⟶ object (C:=C) q :=
  (ComponentCoproduct.homologyIsColimit C q).desc (unionCocone q)
omit [SymmetricCategory C] in
@[reassoc (attr:=simp)] lemma inclusion_toStable (p:Skeleton C) (q:ℕ) :
    inclusion p q ≫ toStable q=colimit.ι (homologyDiagram q) ((ActionCategory.objEquiv _ _) p) :=
  (ComponentCoproduct.homologyIsColimit C q).fac (unionCocone q) ⟨p⟩
instance epi_toStable (q:ℕ) : Epi (toStable (C:=C) q) where
  left_cancellation f g h := by
    apply colimit.hom_ext
    intro stage
    obtain ⟨component,rfl⟩ := (ActionCategory.objEquiv (Skeleton C) (Skeleton C)).surjective stage
    have hp:=congrArg (fun k=>inclusion component q ≫ k) h
    simp only [←Category.assoc,inclusion_toStable] at hp
    change colimit.ι (homologyDiagram (C:=C) q) ((ActionCategory.objEquiv _ _) component) ≫ f =
      colimit.ι (homologyDiagram (C:=C) q) ((ActionCategory.objEquiv _ _) component) ≫ g
    exact hp
omit [SymmetricCategory C] in
lemma translate_toStable (r p s:Skeleton C) (h:r*p=s) (q:ℕ) :
    SSet.homologyMap (nerveMap (translate r p s h)) Z q ≫ inclusion s q ≫ toStable q =
      inclusion p q ≫ toStable q := by
  rw [inclusion_toStable,inclusion_toStable]
  exact colimit.w (homologyDiagram q) (show (ActionCategory.objEquiv _ _) p ⟶
    (ActionCategory.objEquiv _ _) s from ⟨r,h⟩)
variable {D E:Type} [Category.{0} D] [Category.{0} E]
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma map_comp (F:C⥤D) (G:D⥤E) (q:ℕ) :
    SSet.homologyMap (nerveMap (F⋙G)) Z q=
      SSet.homologyMap (nerveMap F) Z q ≫ SSet.homologyMap (nerveMap G) Z q :=
  by
    change SSet.homologyMap (nerveMap F ≫ nerveMap G) Z q=_
    rw [SSet.homologyMap_comp]
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma map_const (U:D) (q:ℕ) (hq:q≠0) : SSet.homologyMap (nerveMap ((Functor.const C).obj U)) Z q=0 := by
  have h : nerveMap ((Functor.const C).obj U)=SSet.const (nerveEquiv.symm U) := by
    ext n x; rfl
  rw [h]
  exact ConnectedProduct.const_homology_zero _ q hq
end ComponentStable

end

end OAI
