import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.IntervalFunctor

namespace OAI

namespace IntervalBar.Diagram

section

open CategoryTheory MonoidalCategory BraidedCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe u v w

section

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {I J K L : Type w} [Preorder I] [Preorder J] [Preorder K] [Preorder L]
@[simp] lemma map_reindex_id :
    map (I:=I) (reindex (C:=C) (OrderHom.id (α:=J)))=𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq ?_ ?_ ?_
    · rfl
    · apply heq_of_eq; funext i
      apply Iso.ext; apply Hom.ext; intro j k h
      change (A.unit i).hom.app j k h ≫ 𝟙 _ = _
      exact Category.comp_id _
    · apply heq_of_eq; funext i j k hij hjk
      apply Iso.ext; apply Hom.ext; intro l m h
      change 𝟙 _ ≫ (A.cut i j k hij hjk).hom.app l m h = _
      exact Category.id_comp _
  · intro A B f
    apply Hom.ext; intro i j h
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    apply Hom.ext; intro l m hlm
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    simp [map,reindex]
    change (f.app i j h).app l m hlm = 𝟙 _ ≫ (f.app i j h).app l m hlm ≫ 𝟙 _
    simp
@[simp] lemma map_reindex_comp (f : J →o K) (g : K →o L) :
    map (I:=I) (reindex (C:=C) (g.comp f)) = map (reindex g) ⋙ map (reindex f) := by
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq ?_ ?_ ?_
    · rfl
    · apply heq_of_eq; funext i
      apply Iso.ext; apply Hom.ext; intro j k h
      change (A.unit i).hom.app (g (f j)) (g (f k)) _ ≫ 𝟙 _ =
        ((A.unit i).hom.app (g (f j)) (g (f k)) _ ≫ 𝟙 _) ≫ 𝟙 _
      simp
    · apply heq_of_eq; funext i j k hij hjk
      apply Iso.ext; apply Hom.ext; intro l m h
      change 𝟙 _ ≫ (A.cut i j k hij hjk).hom.app (g (f l)) (g (f m)) _ =
        𝟙 _ ≫ (𝟙 _ ≫ (A.cut i j k hij hjk).hom.app (g (f l)) (g (f m)) _)
      simp
  · intro A B h
    apply Hom.ext; intro i j hij
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    apply Hom.ext; intro l m hlm
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    simp [map,reindex]
    change (h.app i j hij).app (g (f l)) (g (f m)) _ =
      𝟙 _ ≫ (h.app i j hij).app (g (f l)) (g (f m)) _ ≫ 𝟙 _
    simp

noncomputable def reindex₂ (f : I →o J) (g : K →o L) :
    Diagram (Diagram C L) J ⥤ Diagram (Diagram C K) I :=
  reindex f ⋙ map (reindex g)

@[simp] lemma reindex₂_id :
    reindex₂ (C:=C) (OrderHom.id (α:=I)) (OrderHom.id (α:=J)) = 𝟭 _ := by
  simp [reindex₂]; rfl

end

open CategoryTheory

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {I₁ I₂ I₃ J₁ J₂ J₃ : Type w}
  [Preorder I₁] [Preorder I₂] [Preorder I₃] [Preorder J₁] [Preorder J₂] [Preorder J₃]

lemma reindex₂_comp (f₁ : I₁ →o I₂) (f₂ : I₂ →o I₃)
    (g₁ : J₁ →o J₂) (g₂ : J₂ →o J₃) :
    reindex₂ (C:=C) (f₂.comp f₁) (g₂.comp g₁) =
      reindex₂ f₂ g₂ ⋙ reindex₂ f₁ g₁ := by
  simp only [reindex₂,reindex_comp,map_reindex_comp,Functor.assoc]
  rw [←Functor.assoc (map (reindex g₂)),←reindex_map,Functor.assoc]

open scoped Simplicial
noncomputable def bisimplicial : (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) ⥤ Cat.{v,max u v} where
  obj n := Cat.of (Diagram (Diagram C (Fin (n.2.unop.len+1))) (Fin (n.1.unop.len+1)))
  map f := (reindex₂ f.1.unop.toOrderHom f.2.unop.toOrderHom).toCatHom
  map_id n := by apply Cat.ext; exact reindex₂_id
  map_comp f g := by
    apply Cat.ext
    exact reindex₂_comp g.1.unop.toOrderHom f.1.unop.toOrderHom
      g.2.unop.toOrderHom f.2.unop.toOrderHom
end

section

open CategoryTheory MonoidalCategory
universe u v w u₁ u₂
variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C]
variable {I : Type w} [Preorder I]

omit [MonoidalCategory C] in
lemma iso_hext {X X' Y Y' : C} (hX : X=X') (hY : Y=Y')
    (f : X ≅ Y) (g : X' ≅ Y') (h : HEq f.hom g.hom) : HEq f g := by
  cases hX; cases hY
  exact heq_of_eq (Iso.ext (eq_of_heq h))

lemma hom_hext {A A' B B' : Diagram C I} (hA : A=A') (hB : B=B')
    (f : A ⟶ B) (g : A' ⟶ B') (h : ∀ i j hij, HEq (f.app i j hij) (g.app i j hij)) :
    HEq f g := by
  cases hA; cases hB
  exact heq_of_eq (Hom.ext (fun i j hij => eq_of_heq (h i j hij)))

lemma hfunext {α : Sort u₁} {β β' : α → Sort u₂} {f : ∀ a, β a} {g : ∀ a, β' a}
    (h : ∀ a, HEq (f a) (g a)) : HEq f g :=
  Function.hfunext rfl (by intro a b hab; cases hab; exact h a)
end

open CategoryTheory MonoidalCategory BraidedCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe u v w

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {I J K : Type w} [Preorder I] [Preorder J] [Preorder K]

noncomputable instance reindex₂Braided {L : Type w} [Preorder L]
    (f : I →o J) (g : K →o L) : (reindex₂ (C:=C) f g).Braided := by
  unfold reindex₂
  infer_instance

@[simp] lemma map_ε_app {D : Type*} [Groupoid D] [MonoidalCategory D] [SymmetricCategory D]
    (F : C ⥤ D) [F.Braided] (i j : I) (h : i≤j) :
    (ε (map (I:=I) F)).app i j h = ε F := rfl

@[simp] lemma map_η_app {D : Type*} [Groupoid D] [MonoidalCategory D] [SymmetricCategory D]
    (F : C ⥤ D) [F.Braided] (i j : I) (h : i≤j) :
    (η (map (I:=I) F)).app i j h = η F := by
  apply (cancel_mono (ε F)).mp
  have hh := congrArg (fun f : (map (I:=I) F).obj (𝟙_ (Diagram C I)) ⟶
    (map (I:=I) F).obj (𝟙_ (Diagram C I)) => f.app i j h)
    (Functor.Monoidal.η_ε (map (I:=I) F))
  simp only [comp_app,map_ε_app,id_app] at hh
  simpa only [Functor.Monoidal.η_ε, map, mapObj, tensorUnit_obj] using hh

@[simp] lemma map_μ_app {D : Type*} [Groupoid D] [MonoidalCategory D] [SymmetricCategory D]
    (F : C ⥤ D) [F.Braided] (A B : Diagram C I) (i j : I) (h : i≤j) :
    (μ (map (I:=I) F) A B).app i j h = μ F (A.obj i j h) (B.obj i j h) := rfl

@[simp] lemma reindex_η_app (f : I →o J) (i j : I) (h : i≤j) :
    (η (reindex (C:=C) f)).app i j h = 𝟙 _ := rfl

@[simp] lemma reindex_μ_app (f : I →o J) (A B : Diagram C J) (i j : I) (h : i≤j) :
    (μ (reindex (C:=C) f) A B).app i j h = 𝟙 _ := rfl

omit [SymmetricCategory C] in
@[simp] lemma reindex_map_app (f : I →o J) {A B : Diagram C J} (g : A ⟶ B)
    (i j : I) (h : i≤j) : ((reindex f).map g).app i j h = g.app (f i) (f j) (f.monotone h) := rfl

omit [SymmetricCategory C] in
@[simp] lemma map_map_app {D : Type*} [Groupoid D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] {A B : Diagram C I} (g : A ⟶ B)
    (i j : I) (h : i≤j) : ((map F).map g).app i j h = F.map (g.app i j h) := rfl

omit [SymmetricCategory C] in
@[simp] lemma map_obj {D : Type*} [Groupoid D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] (A : Diagram C I) : (map F).obj A = mapObj F A := rfl

private lemma reindex₂_η_app {L : Type w} [Preorder L]
    (f : I →o J) (g : K →o L) (i j : I) (h : i ≤ j)
    (k l : K) (hkl : k ≤ l) :
    ((η (reindex₂ (C:=C) f g)).app i j h).app k l hkl = 𝟙 _ := by
  change (((map (reindex g)).map (η (reindex f)) ≫ η (map (reindex g))).app i j h).app k l hkl = _
  erw [comp_app, map_map_app (C:=Diagram C L) (I:=I) (reindex g),
    map_η_app (C:=Diagram C L) (I:=I) (reindex g) i j h,
    reindex_map_app (C:=C) g, reindex_η_app (C:=Diagram C L) f i j h,
    reindex_η_app (C:=C) g k l hkl]
  change 𝟙 (𝟙_ C) ≫ 𝟙 (𝟙_ C) = 𝟙 (𝟙_ C)
  exact Category.id_comp _

private lemma map_reindex₂_unit_app {J' K' : Type w} [Preorder J'] [Preorder K']
    (f : J →o J') (g : K →o K') (A : Diagram (Diagram (Diagram C K') J') I)
    (i : I) (j k : J) (h : j ≤ k) (l m : K) (hlm : l ≤ m) :
    ((((map (reindex₂ f g)).obj A).unit i).hom.app j k h).app l m hlm =
      ((A.unit i).hom.app (f j) (f k) (f.monotone h)).app (g l) (g m) (g.monotone hlm) := by
  change (((reindex₂ f g).map (A.unit i).hom ≫ η (reindex₂ f g)).app j k h).app l m hlm = _
  erw [comp_app, reindex₂_η_app]
  change ((A.unit i).hom.app (f j) (f k) (f.monotone h)).app (g l) (g m) (g.monotone hlm) ≫ 𝟙 _ = _
  exact Category.comp_id _

@[simp] lemma map_reindex₂_id :
    map (I:=I) (reindex₂ (C:=C) (OrderHom.id (α:=J)) (OrderHom.id (α:=K)))=𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq ?_ ?_ ?_
    · funext i j h
      exact congrArg (fun F => F.obj (A.obj i j h)) reindex₂_id
    · apply hfunext; intro i
      apply iso_hext (congrArg (fun F => F.obj (A.obj i i le_rfl)) reindex₂_id) rfl
      apply hom_hext (congrArg (fun F => F.obj (A.obj i i le_rfl)) reindex₂_id) rfl
      intro j k h
      apply hom_hext rfl rfl
      intro l m hlm
      apply heq_of_eq
      exact map_reindex₂_unit_app (OrderHom.id (α:=J)) (OrderHom.id (α:=K)) A i j k h l m hlm
    · apply hfunext; intro i
      apply hfunext; intro j
      apply hfunext; intro k
      apply hfunext; intro hij
      apply hfunext; intro hjk
      refine iso_hext ?_ ?_ _ _ ?_
      · exact congrArg₂ (fun X Y => X ⊗ Y)
          (congrArg (fun F => F.obj (A.obj i j hij)) reindex₂_id)
          (congrArg (fun F => F.obj (A.obj j k hjk)) reindex₂_id)
      · exact congrArg (fun F => F.obj (A.obj i k (hij.trans hjk))) reindex₂_id
      refine hom_hext ?_ ?_ _ _ ?_
      · exact congrArg₂ (fun X Y => X ⊗ Y)
          (congrArg (fun F => F.obj (A.obj i j hij)) reindex₂_id)
          (congrArg (fun F => F.obj (A.obj j k hjk)) reindex₂_id)
      · exact congrArg (fun F => F.obj (A.obj i k (hij.trans hjk))) reindex₂_id
      intro l m hlm
      apply hom_hext rfl rfl
      intro n p hnp
      apply heq_of_eq
      change (𝟙 _ ≫ 𝟙 _) ≫ ((A.cut i j k hij hjk).hom.app l m hlm).app n p hnp =
        ((A.cut i j k hij hjk).hom.app l m hlm).app n p hnp
      simp only [Category.id_comp]
  · intro A B f
    apply Hom.ext; intro i j h
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    apply Hom.ext; intro l m hlm
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    apply Hom.ext; intro n p hnp
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    simp only [map, reindex₂, reindex]
    erw [Category.id_comp, Category.comp_id]
    rfl

variable {J₁ J₂ J₃ K₁ K₂ K₃ : Type w}
  [Preorder J₁] [Preorder J₂] [Preorder J₃] [Preorder K₁] [Preorder K₂] [Preorder K₃]
lemma map_reindex₂_comp (f₁ : J₁ →o J₂) (f₂ : J₂ →o J₃)
    (g₁ : K₁ →o K₂) (g₂ : K₂ →o K₃) :
    map (I:=I) (reindex₂ (C:=C) (f₂.comp f₁) (g₂.comp g₁)) =
      map (reindex₂ f₂ g₂) ⋙ map (reindex₂ f₁ g₁) := by
  have hF := reindex₂_comp (C:=C) f₁ f₂ g₁ g₂
  have hO (X : Diagram (Diagram C K₃) J₃) := congrArg (fun F => F.obj X) hF
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq ?_ ?_ ?_
    · funext i j h; exact hO (A.obj i j h)
    · apply hfunext; intro i
      refine iso_hext (hO (A.obj i i le_rfl)) rfl _ _ ?_
      refine hom_hext (hO (A.obj i i le_rfl)) rfl _ _ ?_
      intro j k h
      apply hom_hext rfl rfl
      intro l m hlm
      apply heq_of_eq
      change ((((map (reindex₂ (f₂.comp f₁) (g₂.comp g₁))).obj A).unit i).hom.app j k h).app l m hlm =
        ((((map (reindex₂ f₁ g₁)).obj ((map (reindex₂ f₂ g₂)).obj A)).unit i).hom.app j k h).app l m hlm
      erw [map_reindex₂_unit_app, map_reindex₂_unit_app, map_reindex₂_unit_app]
      rfl
    · apply hfunext; intro i
      apply hfunext; intro j
      apply hfunext; intro k
      apply hfunext; intro hij
      apply hfunext; intro hjk
      have hx := congrArg₂ (fun X Y => X⊗Y) (hO (A.obj i j hij)) (hO (A.obj j k hjk))
      have hy := hO (A.obj i k (hij.trans hjk))
      refine iso_hext hx hy _ _ ?_
      refine hom_hext hx hy _ _ ?_
      intro l m hlm
      apply hom_hext rfl rfl
      intro n p hnp
      apply heq_of_eq
      change (𝟙 _ ≫ 𝟙 _) ≫
          ((A.cut i j k hij hjk).hom.app (f₂ (f₁ l)) (f₂ (f₁ m)) _).app (g₂ (g₁ n)) (g₂ (g₁ p)) _ =
        (𝟙 _ ≫ 𝟙 _) ≫ ((𝟙 _ ≫ 𝟙 _) ≫
          ((A.cut i j k hij hjk).hom.app (f₂ (f₁ l)) (f₂ (f₁ m)) _).app (g₂ (g₁ n)) (g₂ (g₁ p)) _)
      simp
  · intro A B f
    apply Hom.ext; intro i j h
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    apply Hom.ext; intro l m hlm
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    apply Hom.ext; intro n p hnp
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    simp only [map, reindex₂, reindex]
    erw [Category.id_comp, Category.comp_id]
    rfl

noncomputable def reindex₃ (f : I →o J) (g : J₁ →o J₂) (h : K₁ →o K₂) :
    Diagram (Diagram (Diagram C K₂) J₂) J ⥤ Diagram (Diagram (Diagram C K₁) J₁) I :=
  reindex f ⋙ map (reindex₂ g h)

@[simp] lemma reindex₃_id : reindex₃ (C:=C) (OrderHom.id (α:=I))
    (OrderHom.id (α:=J)) (OrderHom.id (α:=K))=𝟭 _ := by
  simp [reindex₃]; rfl

variable {I₁ I₂ I₃ : Type w} [Preorder I₁] [Preorder I₂] [Preorder I₃]
lemma reindex₃_comp (e₁ : I₁ →o I₂) (e₂ : I₂ →o I₃)
    (f₁ : J₁ →o J₂) (f₂ : J₂ →o J₃) (g₁ : K₁ →o K₂) (g₂ : K₂ →o K₃) :
    reindex₃ (C:=C) (e₂.comp e₁) (f₂.comp f₁) (g₂.comp g₁) =
      reindex₃ e₂ f₂ g₂ ⋙ reindex₃ e₁ f₁ g₁ := by
  simp only [reindex₃,reindex_comp,map_reindex₂_comp,Functor.assoc]
  rw [←Functor.assoc (map (reindex₂ f₂ g₂)),←reindex_map,Functor.assoc]

open scoped Simplicial
noncomputable def trisimplicial :
    (SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) ⥤ Cat.{v,max u v} where
  obj n := Cat.of (Diagram (Diagram (Diagram C (Fin (n.2.2.unop.len+1)))
    (Fin (n.2.1.unop.len+1))) (Fin (n.1.unop.len+1)))
  map f := (reindex₃ f.1.unop.toOrderHom f.2.1.unop.toOrderHom f.2.2.unop.toOrderHom).toCatHom
  map_id n := by apply Cat.ext; exact reindex₃_id
  map_comp f g := by
    apply Cat.ext
    exact reindex₃_comp g.1.unop.toOrderHom f.1.unop.toOrderHom
      g.2.1.unop.toOrderHom f.2.1.unop.toOrderHom
      g.2.2.unop.toOrderHom f.2.2.unop.toOrderHom

end IntervalBar.Diagram

end OAI
