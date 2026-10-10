import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.StageDiagramCoverage
import OAI.GroupTheory.SimpleAmenable.Simplicial.IntervalEquivalence

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits Opposite
namespace StageNerveColimit

universe u v w
lemma comp_injective {C : Type u} {D : Type v} {K : Type w}
    [Category C] [Category D] [Category K] (F : C ⥤ D) [F.Faithful]
    (hF : Function.Injective F.obj) : Function.Injective (fun G : K ⥤ C => G ⋙ F) := by
  intro G H h
  refine CategoryTheory.Functor.ext (fun X => hF (Functor.congr_obj h X)) ?_
  intro X Y f
  apply F.map_injective
  simpa only [Functor.comp_map,Functor.comp_obj,Functor.map_comp,eqToHom_map] using Functor.congr_hom h f
end StageNerveColimit
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
variable {a n : ℕ}
noncomputable def nerveCocone : Cocone (diagram (a:=a) (n:=n) ⋙ nerveFunctor) :=
  nerveFunctor.mapCocone cocone
noncomputable def nerveIsColimit : IsColimit (nerveCocone (a:=a) (n:=n)) := by
  apply evaluationJointlyReflectsColimits
  intro p
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨S,G,h⟩ := exists_lift x
    exact ⟨S,G,h.symm⟩
  · intro S x y h
    have he : x=y := StageNerveColimit.comp_injective S.forget (forget_injective S) h
    exact ⟨S,𝟙 S,congrArg _ he⟩
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage

variable {a n : ℕ} {S T : Stage a n} (h : S≤T)
noncomputable instance inclusionMonoidal : (inclusion h).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso U V := Iso.refl _
    μIso_hom_natural_left := by intros; apply UniformObject.Hom.ext; simp; rfl
    μIso_hom_natural_right := by intros; apply UniformObject.Hom.ext; simp; rfl
    associativity := by
      intro first second third
      apply UniformObject.Hom.ext
      change (Labelled.sumHom (𝟙 _) (𝟙 _) ≫ 𝟙 _ ≫
        Labelled.assocHom first.obj second.obj third.obj) =
        (Labelled.assocHom first.obj second.obj third.obj ≫ Labelled.sumHom (𝟙 _) (𝟙 _) ≫ 𝟙 _)
      simp only [Labelled.sumHom_id,Category.id_comp,Category.comp_id]
    left_unitality := by
      intro object
      apply UniformObject.Hom.ext
      change Labelled.leftHom object.obj =
        Labelled.sumHom (𝟙 _) (𝟙 _) ≫ 𝟙 _ ≫ Labelled.leftHom object.obj
      simp only [Labelled.sumHom_id,Category.id_comp]
    right_unitality := by
      intro object
      apply UniformObject.Hom.ext
      change Labelled.rightHom object.obj =
        Labelled.sumHom (𝟙 _) (𝟙 _) ≫ 𝟙 _ ≫ Labelled.rightHom object.obj
      simp only [Labelled.sumHom_id,Category.id_comp] }
noncomputable instance inclusionBraided : (inclusion h).Braided where
  braided U V := by
    change (𝟙 _ ≫ (inclusion h).map (β_ U V).hom) = (β_ ((inclusion h).obj U) ((inclusion h).obj V)).hom ≫ 𝟙 _
    simp only [Category.id_comp,Category.comp_id]
    apply UniformObject.Hom.ext
    rfl
@[simp] lemma inclusion_η : Functor.OplaxMonoidal.η (inclusion h)=𝟙 _ := rfl
@[simp] lemma inclusion_ε : Functor.LaxMonoidal.ε (inclusion h)=𝟙 _ := rfl
@[simp] lemma inclusion_μ (U V : S.Obj) : Functor.LaxMonoidal.μ (inclusion h) U V=𝟙 _ := rfl
end SimpleAmenable.PolygonObject.LabelledStage.Stage

namespace IntervalBar.Diagram

universe u v w u' v'
variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C]
    {D : Type u'} [Groupoid.{v'} D] [MonoidalCategory D]
    {I : Type w} [Preorder I]
lemma map_obj_injective (F : C ⥤ D) [F.Monoidal] [F.Faithful]
    (hF : Function.Injective F.obj) : Function.Injective (map (I:=I) F).obj := by
  intro A B h
  have ho : A.obj=B.obj := by
    funext i j hij
    apply hF
    exact congrArg (fun X => X.obj i j hij) h
  have hu : HEq ((map F).obj A).unit ((map F).obj B).unit := by rw [h]
  have hc : HEq ((map F).obj A).cut ((map F).obj B).cut := by rw [h]
  cases A with
  | mk ao au ac al ar aa =>
    cases B with
    | mk bo bu bc bl br ba =>
      dsimp at ho
      cases ho
      refine ext_heq (A:=⟨ao,au,ac,al,ar,aa⟩) (B:=⟨ao,bu,bc,bl,br,ba⟩) rfl ?_ ?_
      · apply heq_of_eq
        funext i
        apply Iso.ext
        apply F.map_injective
        have he := congrArg (fun u => (u i).hom) (eq_of_heq hu)
        dsimp [map,mapObj] at he
        exact (cancel_mono (Functor.OplaxMonoidal.η F)).mp he
      · apply heq_of_eq
        funext i j k hij hjk
        apply Iso.ext
        apply F.map_injective
        have he := congrArg (fun c => (c i j k hij hjk).hom) (eq_of_heq hc)
        dsimp [map,mapObj] at he
        exact (cancel_epi (Functor.LaxMonoidal.μ F _ _)).mp he
end IntervalBar.Diagram

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar IntervalBar.Diagram

variable {a n : ℕ} {I : Type} [Preorder I]
lemma map_inclusion_id (S : Stage a n) : Diagram.map (I:=I) (inclusion (le_refl S))=𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq rfl ?_ ?_
    · apply heq_of_eq; funext i; apply Iso.ext; apply UniformObject.Hom.ext
      simp [Diagram.map,mapObj]; rfl
    · apply heq_of_eq; funext i j k hij hjk; apply Iso.ext; apply UniformObject.Hom.ext
      simp [Diagram.map,mapObj]; rfl
  · intro source target arrow; apply Hom.ext; intro first last ordered
    simp only [comp_app,Diagram.eqToHom_app]
    change arrow.app first last ordered = 𝟙 _ ≫ arrow.app first last ordered ≫ 𝟙 _
    simp
lemma map_inclusion_comp {S T U : Stage a n} (h : S≤T) (k : T≤U) :
    Diagram.map (I:=I) (inclusion (h.trans k)) = Diagram.map (inclusion h) ⋙ Diagram.map (inclusion k) := by
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq rfl ?_ ?_
    · apply heq_of_eq; funext i; apply Iso.ext; apply UniformObject.Hom.ext
      simp [Diagram.map,mapObj]; rfl
    · apply heq_of_eq; funext i j k hij hjk; apply Iso.ext; apply UniformObject.Hom.ext
      simp [Diagram.map,mapObj]; rfl
  · intro source target arrow; apply Hom.ext; intro first last ordered
    simp only [comp_app,Diagram.eqToHom_app]
    change (inclusion (h.trans k)).map (arrow.app first last ordered) =
      𝟙 _ ≫ (inclusion (h.trans k)).map (arrow.app first last ordered) ≫ 𝟙 _
    simp
lemma map_inclusion_forget {S T : Stage a n} (h : S≤T) :
    Diagram.map (I:=I) (inclusion h) ⋙ Diagram.map T.forget=Diagram.map S.forget := by
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq rfl ?_ ?_
    · apply heq_of_eq; funext i; apply Iso.ext
      simp [Diagram.map,mapObj]; rfl
    · apply heq_of_eq; funext i j k hij hjk; apply Iso.ext
      simp [Diagram.map,mapObj]; rfl
  · intro source target arrow; apply Hom.ext; intro first last ordered
    simp only [comp_app,Diagram.eqToHom_app]
    change S.forget.map (arrow.app first last ordered) =
      𝟙 _ ≫ S.forget.map (arrow.app first last ordered) ≫ 𝟙 _
    simp
noncomputable def barStage : Stage a n ⥤ Cat.{0,0} where
  obj S := Cat.of (Diagram S.Obj I)
  map h := (Diagram.map (inclusion (leOfHom h))).toCatHom
  map_id S := by apply Cat.ext; exact map_inclusion_id S
  map_comp h k := by apply Cat.ext; exact map_inclusion_comp (leOfHom h) (leOfHom k)
noncomputable def barCocone : Cocone (barStage (a:=a) (n:=n) (I:=I)) where
  pt := Cat.of (Diagram (Labelled a n) I)
  ι := {
    app S := (Diagram.map S.forget).toCatHom
    naturality S T h := by apply Cat.ext; exact map_inclusion_forget (leOfHom h) }
noncomputable def barNerveCocone : Cocone (barStage (a:=a) (n:=n) (I:=I) ⋙ nerveFunctor) :=
  nerveFunctor.mapCocone barCocone
noncomputable def barNerveIsColimit (p : ℕ) :
    IsColimit (barNerveCocone (a:=a) (n:=n) (I:=Fin (p+1))) := by
  apply evaluationJointlyReflectsColimits
  intro q
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨S,G,h⟩ := exists_lift_diagram_family x
    exact ⟨S,G,h.symm⟩
  · intro S x y h
    have he : x=y := StageNerveColimit.comp_injective (Diagram.map S.forget)
      (map_obj_injective S.forget (forget_injective S)) h
    exact ⟨S,𝟙 S,congrArg _ he⟩
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end OAI
