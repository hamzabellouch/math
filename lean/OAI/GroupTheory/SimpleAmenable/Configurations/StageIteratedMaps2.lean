import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.IntervalPullback
import OAI.GroupTheory.SimpleAmenable.Simplicial.StageNerveColimit

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar IntervalBar.Diagram

variable {a n : ℕ} {I J K : Type} [Preorder I] [Preorder J] [Preorder K]
lemma map₂_inclusion_id (S : Stage a n) :
    Diagram.map (I:=J) (Diagram.map (I:=I) (inclusion (le_refl S)))=𝟭 _ := by
  have he (X : Diagram S.Obj I) : mapObj (inclusion (le_refl S)) X=X :=
    congrArg (fun F => F.obj X) (map_inclusion_id S)
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq ?_ ?_ ?_
    · funext i j h; exact he _
    · apply hfunext; intro i
      apply iso_hext (he _) rfl
      apply hom_hext (he _) rfl
      intro j k h
      apply heq_of_eq
      change (inclusion (le_refl S)).map ((A.unit i).hom.app j k h) ≫
        (Functor.OplaxMonoidal.η (Diagram.map (I:=I) (inclusion (le_refl S)))).app j k h =
        (A.unit i).hom.app j k h
      rw [map_η_app,inclusion_η]
      apply UniformObject.Hom.ext
      exact Category.comp_id _
    · apply hfunext; intro i
      apply hfunext; intro j
      apply hfunext; intro k
      apply hfunext; intro hij
      apply hfunext; intro hjk
      apply iso_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _) (he _)) (he _)
      apply hom_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _) (he _)) (he _)
      intro l m h
      simp [mapObj]; rfl
  · intro A B f
    apply Hom.ext; intro i j h
    apply Hom.ext; intro k l hkl
    simp only [comp_app,Diagram.eqToHom_app]
    change (f.app i j h).app k l hkl = 𝟙 _ ≫ (f.app i j h).app k l hkl ≫ 𝟙 _
    simp
lemma map₂_inclusion_comp_obj {S T U : Stage a n} (h : S≤T) (k : T≤U)
    (A : Diagram (Diagram S.Obj I) J) :
    mapObj (Diagram.map (I:=I) (inclusion (h.trans k))) A =
      mapObj (Diagram.map (inclusion k)) (mapObj (Diagram.map (inclusion h)) A) := by
  have he (X : Diagram S.Obj I) : mapObj (inclusion (h.trans k)) X=
    mapObj (inclusion k) (mapObj (inclusion h) X) :=
  congrArg (fun F => F.obj X) (map_inclusion_comp h k)
  refine ext_heq ?_ ?_ ?_
  · funext i j h; exact he _
  · apply hfunext; intro i
    apply iso_hext (he _) rfl
    apply hom_hext (he _) rfl
    intro first last ordered
    apply heq_of_eq
    change (inclusion (h.trans k)).map ((A.unit i).hom.app first last ordered) ≫
      (Functor.OplaxMonoidal.η (Diagram.map (I:=I) (inclusion (h.trans k)))).app first last ordered =
      (inclusion k).map ((inclusion h).map ((A.unit i).hom.app first last ordered) ≫
        (Functor.OplaxMonoidal.η (Diagram.map (I:=I) (inclusion h))).app first last ordered) ≫
      (Functor.OplaxMonoidal.η (Diagram.map (I:=I) (inclusion k))).app first last ordered
    simp only [map_η_app,inclusion_η]
    rfl
  · apply hfunext; intro i
    apply hfunext; intro j
    apply hfunext; intro k
    apply hfunext; intro hij
    apply hfunext; intro hjk
    apply iso_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _) (he _)) (he _)
    apply hom_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _) (he _)) (he _)
    intro l m h
    simp [mapObj]; rfl
lemma map₂_inclusion_comp {S T U : Stage a n} (h : S≤T) (k : T≤U) :
    Diagram.map (I:=J) (Diagram.map (I:=I) (inclusion (h.trans k)))=
      Diagram.map (Diagram.map (inclusion h)) ⋙ Diagram.map (Diagram.map (inclusion k)) := by
  refine CategoryTheory.Functor.hext (map₂_inclusion_comp_obj h k) ?_
  intro A B f
  apply hom_hext (map₂_inclusion_comp_obj h k A) (map₂_inclusion_comp_obj h k B)
  intro i j hij
  apply hom_hext
    (congrArg (fun F => F.obj (A.obj i j hij)) (map_inclusion_comp h k))
    (congrArg (fun F => F.obj (B.obj i j hij)) (map_inclusion_comp h k))
  intro l m hlm
  rfl
lemma map₂_inclusion_forget_obj {S T : Stage a n} (h : S≤T)
    (A : Diagram (Diagram S.Obj I) J) :
    mapObj (Diagram.map T.forget) (mapObj (Diagram.map (I:=I) (inclusion h)) A)=
      mapObj (Diagram.map S.forget) A := by
  have he (X : Diagram S.Obj I) : mapObj T.forget (mapObj (inclusion h) X)=mapObj S.forget X :=
  congrArg (fun F => F.obj X) (map_inclusion_forget h)
  refine ext_heq ?_ ?_ ?_
  · funext i j h; exact he _
  · apply hfunext; intro i
    apply iso_hext (he _) rfl
    apply hom_hext (he _) rfl
    intro first last ordered
    apply heq_of_eq
    change T.forget.map ((inclusion h).map ((A.unit i).hom.app first last ordered) ≫
      (Functor.OplaxMonoidal.η (Diagram.map (I:=I) (inclusion h))).app first last ordered) ≫
      (Functor.OplaxMonoidal.η (Diagram.map (I:=I) T.forget)).app first last ordered =
      S.forget.map ((A.unit i).hom.app first last ordered) ≫
      (Functor.OplaxMonoidal.η (Diagram.map (I:=I) S.forget)).app first last ordered
    simp only [map_η_app,inclusion_η,forget_η]
    rfl
  · apply hfunext; intro i
    apply hfunext; intro j
    apply hfunext; intro k
    apply hfunext; intro hij
    apply hfunext; intro hjk
    apply iso_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _) (he _)) (he _)
    apply hom_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _) (he _)) (he _)
    intro l m h
    simp [mapObj]; rfl
lemma map₂_inclusion_forget {S T : Stage a n} (h : S≤T) :
    Diagram.map (I:=J) (Diagram.map (I:=I) (inclusion h)) ⋙
      Diagram.map (Diagram.map T.forget)=Diagram.map (Diagram.map S.forget) := by
  refine CategoryTheory.Functor.hext (map₂_inclusion_forget_obj h) ?_
  intro A B f
  apply hom_hext (map₂_inclusion_forget_obj h A) (map₂_inclusion_forget_obj h B)
  intro i j hij
  apply hom_hext
    (congrArg (fun F => F.obj (A.obj i j hij)) (map_inclusion_forget h))
    (congrArg (fun F => F.obj (B.obj i j hij)) (map_inclusion_forget h))
  intro l m hlm
  rfl
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end

end OAI
