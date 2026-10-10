import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.StageTripleHomology
import OAI.GroupTheory.SimpleAmenable.Simplicial.RestrictedMonoidalTranspose

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace RestrictedNerve
open IntervalBar IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
lemma diagram_map_obj {D E : Type} [Groupoid D] [Groupoid E]
    [MonoidalCategory D] [MonoidalCategory E] {I : Type} [Preorder I]
    (F : D ⥤ E) [F.Monoidal] (A : Diagram D I) :
    (Diagram.map F).obj A = mapObj F A := rfl
variable {I J K : Type} [Preorder I] [Preorder J] [Preorder K]
private lemma map₂_reindex_unit_app {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1))
    (A : Diagram (Diagram (Strings W m) I) J) (i : J)
    (j k : I) (h : j ≤ k) (t : Fin (n+1)) :
    ((((Diagram.map (Diagram.map (reindex W u))).obj A).unit i).hom.app j k h).hom.app t =
      ((A.unit i).hom.app j k h).hom.app (u.obj t) := by
  change (((Diagram.map (reindex W u)).map (A.unit i).hom ≫
    Functor.OplaxMonoidal.η (Diagram.map (reindex W u))).app j k h).hom.app t = _
  erw [comp_app, map_η_app (I:=I) (reindex W u)]
  change ((A.unit i).hom.app j k h).hom.app (u.obj t) ≫ 𝟙 _ = _
  exact Category.comp_id _

private lemma map₂_reindex_cut_app {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1))
    (A : Diagram (Diagram (Strings W m) I) J) (i j k : J)
    (hij : i ≤ j) (hjk : j ≤ k) (l r : I) (h : l ≤ r) (t : Fin (n+1)) :
    ((((Diagram.map (Diagram.map (reindex W u))).obj A).cut i j k hij hjk).hom.app l r h).hom.app t =
      ((A.cut i j k hij hjk).hom.app l r h).hom.app (u.obj t) := by
  change 𝟙 _ ≫ ((A.cut i j k hij hjk).hom.app l r h).hom.app (u.obj t) = _
  exact Category.id_comp _

private lemma map₃_reindex_unit_app {q₁ q₂ q₃ n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1))
    (A : Diagram (Diagram (Diagram (Strings W m) (Fin (q₁+1))) (Fin (q₂+1))) (Fin (q₃+1))) (i : (Fin (q₃+1)))
    (j k : (Fin (q₂+1))) (h : j ≤ k) (l r : (Fin (q₁+1))) (hlr : l ≤ r) (t : Fin (n+1)) :
    (((((Diagram.map (I:=(Fin (q₃+1))) (Diagram.map (I:=(Fin (q₂+1))) (Diagram.map (I:=(Fin (q₁+1))) (reindex W u)))).obj A).unit i).hom.app j k h).app l r hlr).hom.app t =
      (((A.unit i).hom.app j k h).app l r hlr).hom.app (u.obj t) := by
  change ((((Diagram.map (I:=(Fin (q₂+1))) (Diagram.map (I:=(Fin (q₁+1))) (reindex W u))).map (A.unit i).hom ≫
    Functor.OplaxMonoidal.η (Diagram.map (I:=(Fin (q₂+1))) (Diagram.map (I:=(Fin (q₁+1))) (reindex W u)))).app j k h).app l r hlr).hom.app t = _
  erw [comp_app, map_η_app (I:=(Fin (q₂+1))) (Diagram.map (I:=(Fin (q₁+1))) (reindex W u))]
  erw [map_η_app (I:=(Fin (q₁+1))) (reindex W u)]
  change (((A.unit i).hom.app j k h).app l r hlr).hom.app (u.obj t) ≫ 𝟙 _ = _
  exact Category.comp_id _

private lemma map₃_reindex_cut_app {q₁ q₂ q₃ n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1))
    (A : Diagram (Diagram (Diagram (Strings W m) (Fin (q₁+1))) (Fin (q₂+1))) (Fin (q₃+1))) (i j k : (Fin (q₃+1)))
    (hij : i ≤ j) (hjk : j ≤ k) (l r : (Fin (q₂+1))) (h : l ≤ r)
    (v w : (Fin (q₁+1))) (hvw : v ≤ w) (t : Fin (n+1)) :
    (((((Diagram.map (I:=(Fin (q₃+1))) (Diagram.map (I:=(Fin (q₂+1))) (Diagram.map (I:=(Fin (q₁+1))) (reindex W u)))).obj A).cut i j k hij hjk).hom.app l r h).app v w hvw).hom.app t =
      (((A.cut i j k hij hjk).hom.app l r h).app v w hvw).hom.app (u.obj t) := by
  change 𝟙 _ ≫ (((A.cut i j k hij hjk).hom.app l r h).app v w hvw).hom.app (u.obj t) = _
  exact Category.id_comp _

lemma map₂_strings_reindex_id (n:ℕ) :
    Diagram.map (I:=J) (Diagram.map (I:=I) (reindex W (𝟭 (Fin (n+1)))))=𝟭 _ := by
  have he (A : Diagram (Strings W n) I) :
      Diagram.mapObj (reindex W (𝟭 (Fin (n+1)))) A=A :=
    congrArg (fun F=>F.obj A) (map_strings_reindex_id W n)
  have he₂ (A : Diagram (Diagram (Strings W n) I) J) :
      (Diagram.map (Diagram.map (reindex W (𝟭 (Fin (n+1)))))).obj A=A := by
    refine ext_heq ?_ ?_ ?_
    · funext i j h; exact he _
    · apply hfunext; intro i
      apply iso_hext (he _) rfl
      apply hom_hext (he _) rfl
      intro j k h
      apply heq_of_eq
      apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      erw [map₂_reindex_unit_app]
      rfl
    · apply hfunext; intro i
      apply hfunext; intro j
      apply hfunext; intro k
      apply hfunext; intro hij
      apply hfunext; intro hjk
      apply iso_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
      apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
      intro l m h
      apply heq_of_eq
      apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      erw [map₂_reindex_cut_app]
      rfl
  refine CategoryTheory.Functor.hext he₂ ?_
  intro A B f
  apply hom_hext (he₂ A) (he₂ B)
  intro i j h
  apply hom_hext (he _) (he _)
  intro l m hlm
  apply heq_of_eq
  apply WideSubcategory.hom_ext; rfl
lemma map₂_strings_reindex_comp {n m k:ℕ} (u:Fin (n+1) ⥤ Fin (m+1)) (v:Fin (m+1) ⥤ Fin (k+1)) :
    Diagram.map (I:=J) (Diagram.map (I:=I) (reindex W (u⋙v))) =
      Diagram.map (Diagram.map (reindex W v)) ⋙ Diagram.map (Diagram.map (reindex W u)) := by
  have he (A : Diagram (Strings W k) I) :
      Diagram.mapObj (reindex W (u⋙v)) A =
        Diagram.mapObj (reindex W u) (Diagram.mapObj (reindex W v) A) :=
    congrArg (fun F=>F.obj A) (map_strings_reindex_comp W u v)
  have he₂ (A : Diagram (Diagram (Strings W k) I) J) :
      (Diagram.map (Diagram.map (reindex W (u⋙v)))).obj A=
        (Diagram.map (Diagram.map (reindex W u))).obj ((Diagram.map (Diagram.map (reindex W v))).obj A) := by
    refine ext_heq ?_ ?_ ?_
    · funext i j h; exact he _
    · apply hfunext; intro i
      apply iso_hext (he _) rfl
      apply hom_hext (he _) rfl
      intro j k h
      apply heq_of_eq
      apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      erw [map₂_reindex_unit_app, map₂_reindex_unit_app, map₂_reindex_unit_app]
      rfl
    · apply hfunext; intro i
      apply hfunext; intro j
      apply hfunext; intro k
      apply hfunext; intro hij
      apply hfunext; intro hjk
      apply iso_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
      apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
      intro l m h
      apply heq_of_eq
      apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      erw [map₂_reindex_cut_app, map₂_reindex_cut_app, map₂_reindex_cut_app]
      rfl
  refine CategoryTheory.Functor.hext he₂ ?_
  intro A B f
  apply hom_hext (he₂ A) (he₂ B)
  intro i j h
  apply hom_hext (he _) (he _)
  intro l m hlm
  apply heq_of_eq
  apply WideSubcategory.hom_ext; rfl
lemma map₃_strings_reindex_id (n q₁ q₂ q₃:ℕ) :
    Diagram.map (I:=(Fin (q₃+1))) (Diagram.map (I:=(Fin (q₂+1))) (Diagram.map (I:=(Fin (q₁+1))) (reindex W (𝟭 (Fin (n+1))))))=𝟭 _ := by
  have he (A : Diagram (Strings W n) (Fin (q₁+1))) :
      Diagram.mapObj (reindex W (𝟭 (Fin (n+1)))) A=A :=
    congrArg (fun F=>F.obj A) (map_strings_reindex_id W n)
  have he₂ (A : Diagram (Diagram (Strings W n) (Fin (q₁+1))) (Fin (q₂+1))) :
      (Diagram.map (Diagram.map (reindex W (𝟭 (Fin (n+1)))))).obj A=A :=
    congrArg (fun F=>F.obj A) (map₂_strings_reindex_id W n)
  have he₃ (A : Diagram (Diagram (Diagram (Strings W n) (Fin (q₁+1))) (Fin (q₂+1))) (Fin (q₃+1))) :
      (Diagram.map (Diagram.map (Diagram.map (reindex W (𝟭 (Fin (n+1))))))).obj A=A := by
    refine ext_heq ?_ ?_ ?_
    · funext i j h; exact he₂ _
    · apply hfunext; intro i
      apply iso_hext (he₂ _) rfl
      apply hom_hext (he₂ _) rfl
      intro j k h
      apply hom_hext (he _) rfl
      intro l m hlm
      apply heq_of_eq
      apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      erw [map₃_reindex_unit_app W]
      rfl
    · apply hfunext; intro i
      apply hfunext; intro j
      apply hfunext; intro k
      apply hfunext; intro hij
      apply hfunext; intro hjk
      apply iso_hext (congrArg₂ (fun X Y=>X⊗Y) (he₂ _) (he₂ _)) (he₂ _)
      apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he₂ _) (he₂ _)) (he₂ _)
      intro l m h
      apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
      intro v w hvw
      apply heq_of_eq
      apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      erw [map₃_reindex_cut_app W]
      rfl
  refine CategoryTheory.Functor.hext he₃ ?_
  intro A B f
  apply hom_hext (he₃ A) (he₃ B)
  intro i j h
  apply hom_hext (he₂ _) (he₂ _)
  intro l m hlm
  apply hom_hext (he _) (he _)
  intro v w hvw
  apply heq_of_eq
  apply WideSubcategory.hom_ext; rfl
private lemma map₃_reindex_comp_cut_app (q₁ q₂ q₃ : ℕ) {n m k : ℕ}
    (u : Fin (n+1) ⥤ Fin (m+1)) (v : Fin (m+1) ⥤ Fin (k+1))
    (A : Diagram (Diagram (Diagram (Strings W k) (Fin (q₁+1))) (Fin (q₂+1))) (Fin (q₃+1)))
    (i j z : Fin (q₃+1)) (hij : i ≤ j) (hjz : j ≤ z)
    (l r : Fin (q₂+1)) (h : l ≤ r)
    (first last : Fin (q₁+1)) (ordered : first ≤ last) (t : Fin (n+1)) :
    (((((Diagram.map (I:=Fin (q₃+1)) (Diagram.map (I:=Fin (q₂+1))
        (Diagram.map (I:=Fin (q₁+1)) (reindex W (u ⋙ v))))).obj A).cut i j z hij hjz).hom.app l r h).app first last ordered).hom.app t =
    (((((Diagram.map (I:=Fin (q₃+1)) (Diagram.map (I:=Fin (q₂+1))
        (Diagram.map (I:=Fin (q₁+1)) (reindex W u)))).obj
          ((Diagram.map (I:=Fin (q₃+1)) (Diagram.map (I:=Fin (q₂+1))
            (Diagram.map (I:=Fin (q₁+1)) (reindex W v)))).obj A)).cut i j z hij hjz).hom.app l r h).app first last ordered).hom.app t := by
  exact (map₃_reindex_cut_app (q₁:=q₁) (q₂:=q₂) (q₃:=q₃) W (u ⋙ v) A
    i j z hij hjz l r h first last ordered t).trans
    ((map₃_reindex_cut_app (q₁:=q₁) (q₂:=q₂) (q₃:=q₃) W u
      ((Diagram.map (I:=Fin (q₃+1)) (Diagram.map (I:=Fin (q₂+1))
        (Diagram.map (I:=Fin (q₁+1)) (reindex W v)))).obj A)
      i j z hij hjz l r h first last ordered t).trans
      (map₃_reindex_cut_app (q₁:=q₁) (q₂:=q₂) (q₃:=q₃) W v A
        i j z hij hjz l r h first last ordered (u.obj t))).symm

private lemma map₃_strings_reindex_comp_obj (q₁ q₂ q₃ : ℕ) {n m k : ℕ}
    (u : Fin (n+1) ⥤ Fin (m+1)) (v : Fin (m+1) ⥤ Fin (k+1))
    (A : Diagram (Diagram (Diagram (Strings W k) (Fin (q₁+1))) (Fin (q₂+1))) (Fin (q₃+1))) :
      (Diagram.map (Diagram.map (Diagram.map (reindex W (u⋙v))))).obj A=
        (Diagram.map (Diagram.map (Diagram.map (reindex W u)))).obj
          ((Diagram.map (Diagram.map (Diagram.map (reindex W v)))).obj A) := by
  have he (A : Diagram (Strings W k) (Fin (q₁+1))) :
      Diagram.mapObj (reindex W (u⋙v)) A =
        Diagram.mapObj (reindex W u) (Diagram.mapObj (reindex W v) A) :=
    congrArg (fun F=>F.obj A) (map_strings_reindex_comp W u v)
  have he₂ (A : Diagram (Diagram (Strings W k) (Fin (q₁+1))) (Fin (q₂+1))) :
      (Diagram.map (Diagram.map (reindex W (u⋙v)))).obj A=
        (Diagram.map (Diagram.map (reindex W u))).obj ((Diagram.map (Diagram.map (reindex W v))).obj A) :=
    congrArg (fun F=>F.obj A) (map₂_strings_reindex_comp W u v)
  refine ext_heq ?_ ?_ ?_
  · funext i j h; exact he₂ _
  · apply hfunext; intro i
    apply iso_hext (he₂ _) rfl
    apply hom_hext (he₂ _) rfl
    intro j k h
    apply hom_hext (he _) rfl
    intro l m hlm
    apply heq_of_eq
    apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
    erw [map₃_reindex_unit_app W, map₃_reindex_unit_app W, map₃_reindex_unit_app W]
    rfl
  · apply hfunext; intro i
    apply hfunext; intro j
    apply hfunext; intro k
    apply hfunext; intro hij
    apply hfunext; intro hjk
    apply iso_hext (congrArg₂ (fun X Y=>X⊗Y) (he₂ _) (he₂ _)) (he₂ _)
    apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he₂ _) (he₂ _)) (he₂ _)
    intro l m h
    apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
    intro first last ordered
    apply heq_of_eq
    apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
    exact map₃_reindex_comp_cut_app W q₁ q₂ q₃ u v A i j k hij hjk l m h first last ordered t

lemma map₃_strings_reindex_comp (q₁ q₂ q₃:ℕ) {n m k:ℕ} (u:Fin (n+1) ⥤ Fin (m+1)) (v:Fin (m+1) ⥤ Fin (k+1)) :
    Diagram.map (I:=(Fin (q₃+1))) (Diagram.map (I:=(Fin (q₂+1))) (Diagram.map (I:=(Fin (q₁+1))) (reindex W (u⋙v)))) =
      Diagram.map (Diagram.map (Diagram.map (reindex W v))) ⋙ Diagram.map (Diagram.map (Diagram.map (reindex W u))) := by
  have he (A : Diagram (Strings W k) (Fin (q₁+1))) :
      Diagram.mapObj (reindex W (u⋙v)) A =
        Diagram.mapObj (reindex W u) (Diagram.mapObj (reindex W v) A) :=
    congrArg (fun F=>F.obj A) (map_strings_reindex_comp W u v)
  have he₂ (A : Diagram (Diagram (Strings W k) (Fin (q₁+1))) (Fin (q₂+1))) :
      (Diagram.map (Diagram.map (reindex W (u⋙v)))).obj A=
        (Diagram.map (Diagram.map (reindex W u))).obj ((Diagram.map (Diagram.map (reindex W v))).obj A) :=
    congrArg (fun F=>F.obj A) (map₂_strings_reindex_comp W u v)
  have he₃ (A : Diagram (Diagram (Diagram (Strings W k) (Fin (q₁+1))) (Fin (q₂+1))) (Fin (q₃+1))) :
      (Diagram.map (Diagram.map (Diagram.map (reindex W (u⋙v))))).obj A=
        (Diagram.map (Diagram.map (Diagram.map (reindex W u)))).obj
          ((Diagram.map (Diagram.map (Diagram.map (reindex W v)))).obj A) :=
    map₃_strings_reindex_comp_obj W q₁ q₂ q₃ u v A
  refine CategoryTheory.Functor.hext he₃ ?_
  intro A B f
  apply hom_hext (he₃ A) (he₃ B)
  intro i j h
  apply hom_hext (he₂ _) (he₂ _)
  intro l m hlm
  apply hom_hext (he _) (he _)
  intro v w hvw
  apply heq_of_eq
  apply WideSubcategory.hom_ext; rfl
lemma bar₃Map_strings_reindex_id (n:ℕ) :
    bar₃Map (reindex W (𝟭 (Fin (n+1))))=𝟙 _ := by
  ext q x
  exact congrArg (fun T => x ⋙ T)
    (map₃_strings_reindex_id W n q.unop.len q.unop.len q.unop.len)
lemma bar₃Map_strings_reindex_comp {n m k:ℕ} (u:Fin (n+1) ⥤ Fin (m+1)) (v:Fin (m+1) ⥤ Fin (k+1)) :
    bar₃Map (reindex W (u⋙v))=bar₃Map (reindex W v) ≫ bar₃Map (reindex W u) := by
  ext q x
  exact congrArg (fun T => x ⋙ T)
    (map₃_strings_reindex_comp W q.unop.len q.unop.len q.unop.len u v)

noncomputable def tripleHorizontal : SimplexCategoryᵒᵖ ⥤ SSet where
  obj p := bar₃ (C:=Strings W p.unop.len)
  map f := bar₃Map (reindex W f.unop.toOrderHom.toFunctor)
  map_id p := bar₃Map_strings_reindex_id W p.unop.len
  map_comp f g := bar₃Map_strings_reindex_comp W g.unop.toOrderHom.toFunctor f.unop.toOrderHom.toFunctor
end RestrictedNerve

end OAI
