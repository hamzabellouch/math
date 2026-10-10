import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.BarContractible
import OAI.GroupTheory.SimpleAmenable.Simplicial.LabelledMonoidal

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace IntervalBar.Diagram

variable {C D : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
  [Groupoid.{0} D] [MonoidalCategory D] [SymmetricCategory D]
variable {I J K L : Type} [Preorder I] [Preorder J] [Preorder K] [Preorder L]
private lemma map_reindex_unit_app (f : I →o J)
    (A : Diagram (Diagram (Diagram C J) K) L) (i : L)
    (j k : K) (h : j ≤ k) (l m : I) (hlm : l ≤ m) :
    ((((map (map (reindex f))).obj A).unit i).hom.app j k h).app l m hlm =
      ((A.unit i).hom.app j k h).app (f l) (f m) (f.monotone hlm) := by
  change (((map (reindex f)).map (A.unit i).hom ≫
    Functor.OplaxMonoidal.η (map (reindex f))).app j k h).app l m hlm = _
  erw [comp_app, map_η_app (I:=K) (reindex (C:=C) f)]
  change ((A.unit i).hom.app j k h).app (f l) (f m) (f.monotone hlm) ≫ 𝟙 _ = _
  exact Category.comp_id _

private lemma map_triple_unit_app (F : C ⥤ D) [F.Braided]
    (A : Diagram (Diagram (Diagram C J) K) L) (i : L)
    (j k : K) (h : j ≤ k) (l m : J) (hlm : l ≤ m) :
    ((((map (map (map F))).obj A).unit i).hom.app j k h).app l m hlm =
      F.map (((A.unit i).hom.app j k h).app l m hlm) ≫ Functor.OplaxMonoidal.η F := by
  change (((map (map F)).map (A.unit i).hom ≫
    Functor.OplaxMonoidal.η (map (map F))).app j k h).app l m hlm = _
  erw [comp_app, map_η_app (I:=K) (map (I:=J) F), map_η_app (I:=J) F]
  rfl

lemma map_map_map_reindex (F : C ⥤ D) [F.Braided] (f : I →o J) :
    map (I:=L) (map (I:=K) (map (I:=J) F)) ⋙ map (map (reindex f)) =
      map (map (reindex f)) ⋙ map (map (map (I:=I) F)) := by
  have he (X : Diagram (Diagram C J) K) :
      mapObj (map F) (mapObj (reindex f) X) = mapObj (reindex f) (mapObj (map F) X) :=
    congrArg (fun T => T.obj X) (map_map_reindex F f).symm
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq ?_ ?_ ?_
    · funext i j h; exact (he _).symm
    · apply hfunext; intro i
      apply iso_hext (he _).symm rfl
      apply hom_hext (he _).symm rfl
      intro j k h
      apply hom_hext rfl rfl
      intro l m hlm
      apply heq_of_eq
      erw [map_reindex_unit_app, map_triple_unit_app,
        map_triple_unit_app, map_reindex_unit_app]
      rfl
    · apply hfunext; intro i
      apply hfunext; intro j
      apply hfunext; intro k
      apply hfunext; intro hij
      apply hfunext; intro hjk
      apply iso_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _).symm (he _).symm) (he _).symm
      apply hom_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _).symm (he _).symm) (he _).symm
      intro l m hlm
      apply hom_hext rfl rfl
      intro n p hnp
      apply heq_of_eq
      change 𝟙 _ ≫ (Functor.LaxMonoidal.μ F _ _ ≫
          F.map (((A.cut i j k hij hjk).hom.app l m hlm).app (f n) (f p) _)) =
        Functor.LaxMonoidal.μ F _ _ ≫
          F.map (𝟙 _ ≫ ((A.cut i j k hij hjk).hom.app l m hlm).app (f n) (f p) _)
      erw [Category.id_comp, Category.id_comp]
  · intro A B g
    apply Hom.ext; intro i j h
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    apply Hom.ext; intro k l hkl
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    apply Hom.ext; intro m n hmn
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    simp only [map,reindex]
    erw [Category.id_comp, Category.comp_id]
    rfl
lemma barMap_map_map_reindex (F : C ⥤ D) [F.Braided] (f : I →o J) :
    barMap (map (I:=K) (map (I:=J) F)) ≫ barMap (map (reindex f)) =
      barMap (map (reindex f)) ≫ barMap (map (map (I:=I) F)) := by
  have he : simplicialMap (map (I:=K) (map (I:=J) F)) ≫ simplicialMap (map (reindex f)) =
      simplicialMap (map (reindex f)) ≫ simplicialMap (map (map (I:=I) F)) := by
    apply NatTrans.ext; funext p; apply Cat.ext
    exact map_map_map_reindex F f
  have h := congrArg SimplicialDiagonal.nerveDiagonal.map he
  erw [Functor.map_comp, Functor.map_comp] at h
  exact h
lemma bar₂Map_map_reindex (F : C ⥤ D) [F.Braided] (f : I →o J) :
    bar₂Map (map (I:=J) F) ≫ bar₂Map (reindex f) =
      bar₂Map (reindex f) ≫ bar₂Map (map (I:=I) F) := by
  have he : rows₂Map (map (I:=J) F) ≫ rows₂Map (reindex f) =
      rows₂Map (reindex f) ≫ rows₂Map (map (I:=I) F) := by
    apply NatTrans.ext; funext p
    exact barMap_map_map_reindex F f
  have h := congrArg SimplicialDiagonal.diagonal.map he
  erw [Functor.map_comp, Functor.map_comp] at h
  exact h
noncomputable def rows₃Map (F : C ⥤ D) [F.Braided] : rows₃ (C:=C) ⟶ rows₃ (C:=D) where
  app p := bar₂Map (map (I:=Fin (p.unop.len+1)) F)
  naturality _ _ f := (bar₂Map_map_reindex F f.unop.toOrderHom).symm
noncomputable def bar₃Map (F : C ⥤ D) [F.Braided] : bar₃ (C:=C) ⟶ bar₃ (C:=D) :=
  SimplicialDiagonal.diagonal.map (rows₃Map F)
lemma bar₃Map_homology_isIso (F : C ⥤ D) [F.Braided] [F.IsEquivalence] (n : ℕ) :
    IsIso (SSet.homologyMap (bar₃Map F) DiagonalResolution.Z n) := by
  apply SimplicialDiagonal.homologyMap_isIso
  intro p q
  exact bar₂Map_homology_isIso (map (I:=Fin (p.unop.len+1)) F) q
end IntervalBar.Diagram

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject

variable {a n : ℕ}
noncomputable def stringEval : StringGroupoid a n ⥤ PolygonObject a where
  obj F := F.obj.obj 0
  map f := f.hom.app 0
  map_id _ := rfl
  map_comp _ _ := rfl
instance : (stringEval (a:=a) (n:=n)).Faithful where
  map_injective h := by apply WideSubcategory.hom_ext; exact ladder_ext h
noncomputable instance : (stringEval (a:=a) (n:=n)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso _ _ := Iso.refl _
    μIso_hom_natural_left := by intros; simp; rfl
    μIso_hom_natural_right := by intros; simp; rfl
    associativity := by
      intro first second third
      change (𝟙 _ ▷ _ ≫ 𝟙 _ ≫ (α_ _ _ _).hom) =
        ((α_ _ _ _).hom ≫ _ ◁ 𝟙 _ ≫ 𝟙 _)
      simp
    left_unitality := by
      intro object
      change (λ_ _).hom = 𝟙 _ ▷ _ ≫ 𝟙 _ ≫ (λ_ _).hom
      simp
    right_unitality := by
      intro object
      change (ρ_ _).hom = _ ◁ 𝟙 _ ≫ 𝟙 _ ≫ (ρ_ _).hom
      simp }
noncomputable instance : (stringEval (a:=a) (n:=n)).Braided where
  braided _ _ := by
    change sumSwap _ _ ≫ 𝟙 _ = 𝟙 _ ≫ sumSwap _ _
    simp
lemma pointShift_sum_left {U V W T : PolygonObject a} (f : U ⟶ W) (g : V ⟶ T) (x : U.Point) :
    pointShift (sumArrow f g) (sumPointEquiv U V (.inl x))=pointShift f x := by
  simpa only [pointShift_reduced] using pointShift_unique (sumArrow f g) _ (pointShift f x)
    (by simpa only [sumArrow_inl,sumPointEquiv_inl] using pointShift_spec f x)
lemma pointShift_sum_right {U V W T : PolygonObject a} (f : U ⟶ W) (g : V ⟶ T) (x : V.Point) :
    pointShift (sumArrow f g) (sumPointEquiv U V (.inr x))=pointShift g x := by
  simpa only [pointShift_reduced] using pointShift_unique (sumArrow f g) _ (pointShift g x)
    (by simpa only [sumArrow_inr,sumPointEquiv_inr] using pointShift_spec g x)
lemma increments_sum_left (F G : RawString a n) (x : (F.obj 0).Point) :
    increments (F⊗G) (sumPointEquiv (F.obj 0) (G.obj 0) (.inl x))=increments F x := by
  funext i
  simp only [increments,trajectoryShift]
  change pointShift (sumArrow _ _) _ - pointShift (sumArrow _ _) _ = _
  rw [pointShift_sum_left,pointShift_sum_left]
  rfl
lemma increments_sum_right (F G : RawString a n) (x : (G.obj 0).Point) :
    increments (F⊗G) (sumPointEquiv (F.obj 0) (G.obj 0) (.inr x))=increments G x := by
  funext i
  simp only [increments,trajectoryShift]
  change pointShift (sumArrow _ _) _ - pointShift (sumArrow _ _) _ = _
  rw [pointShift_sum_right,pointShift_sum_right]
  rfl
namespace Labelled
noncomputable def tensorInitial (U V : Labelled a n) :
    ((string U ⊗ string V).obj.obj 0) ⟶ (string (U⊗V)).obj.obj 0 :=
  inv (C := PolygonObject a) (sumArrow (initial U) (initial V))
    (I := IsIso.of_groupoid (C := PolygonObject a) _) ≫ initial (U⊗V)
lemma tensorInitial_positional (U V : Labelled a n) : Positional (tensorInitial U V) :=
  positional_comp (positional_inv (sumArrow_positional (incrementInitial_positional _ _)
    (incrementInitial_positional _ _))) (incrementInitial_positional _ _)
lemma tensorInitial_labels (U V : Labelled a n) (x : ((string U ⊗ string V).obj.obj 0).Point) :
    increments (string (U⊗V)).obj ((tensorInitial U V).toEquiv x) =
      increments (string U ⊗ string V).obj x := by
  obtain ⟨y,rfl⟩ := (sumArrow (initial U) (initial V)).toEquiv.surjective x
  change increments (string (sum U V)).obj ((initial (sum U V)).toEquiv
    ((inv (C := PolygonObject a) (sumArrow (initial U) (initial V))
      (I := IsIso.of_groupoid (C := PolygonObject a) _)).toEquiv
      ((sumArrow (initial U) (initial V)).toEquiv y))) =
    increments ((string U).obj ⊗ (string V).obj) ((sumArrow (initial U) (initial V)).toEquiv y)
  rw [inv_arrow_apply,Equiv.symm_apply_apply,incrementString_spec_reduced _ _ (sum U V).reduced]
  obtain ⟨z,rfl⟩ := (sumPointEquiv U.polygon V.polygon).surjective y
  cases z with
  | inl z =>
    rw [sumArrow_inl]
    rw [increments_sum_left,incrementString_spec_reduced _ _ U.reduced]
    exact sum_label_left U V z
  | inr z =>
    rw [sumArrow_inr]
    rw [increments_sum_right,incrementString_spec_reduced _ _ V.reduced]
    exact sum_label_right U V z
noncomputable def tensorLadder (U V : Labelled a n) : string U⊗string V ⟶ string (U⊗V) :=
  ⟨extendLadder (tensorInitial U V),extendLadder_positional_of_increments _
    (tensorInitial_positional U V) (tensorInitial_labels U V)⟩
@[simp] lemma tensorLadder_zero (U V : Labelled a n) : (tensorLadder U V).hom.app 0=tensorInitial U V :=
  extendLadder_zero _
noncomputable def unitLadder : 𝟙_ (StringGroupoid a n) ⟶ string (𝟙_ (Labelled a n)) :=
  ⟨extendLadder (initial (𝟙_ _)),extendLadder_positional_of_increments _
    (incrementInitial_positional _ _) (by intro x; change PolygonObject.empty.Point at x; exact isEmptyElim x)⟩
@[simp] lemma unitLadder_zero : (unitLadder (a:=a) (n:=n)).hom.app 0=initial (𝟙_ _) := extendLadder_zero _
noncomputable def initialIso : forget (a:=a) (n:=n) ≅ toStrings ⋙ stringEval :=
  NatIso.ofComponents (fun U =>
    @asIso (PolygonObject a) _ _ _ (initial U) (IsIso.of_groupoid (C := PolygonObject a) _)) (by
    intro U V f
    change f.arrow ≫ initial V = initial U ≫ (ladder f).hom.app 0
    rw [ladder_zero]
    simp [initialArrow])
end Labelled
end SimpleAmenable.PolygonObject

end OAI
