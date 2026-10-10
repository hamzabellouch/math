import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.DiagonalComparison
import OAI.GroupTheory.SimpleAmenable.Simplicial.IntervalEssSurj
import OAI.GroupTheory.SimpleAmenable.Simplicial.IntervalExtension
import OAI.GroupTheory.SimpleAmenable.Simplicial.IntervalPullback

namespace OAI

namespace IntervalBar.Diagram

section
open CategoryTheory MonoidalCategory
universe u v u' v'

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {D : Type u'} [Groupoid.{v'} D] [MonoidalCategory D] [SymmetricCategory D]
instance mapFaithful (F : C ⥤ D) [F.Monoidal] [F.Faithful] (n : ℕ) :
    (map (I:=Fin (n+1)) F).Faithful where
  map_injective h := by
    apply Hom.ext
    intro i j hij
    apply F.map_injective
    exact congrArg (fun f => f.app i j hij) h
noncomputable instance mapFull (F : C ⥤ D) [F.Monoidal] [F.Full] (n : ℕ) :
    (map (I:=Fin (n+1)) F).Full where
  map_surjective {X Y} φ := by
    let f : (eval n).obj X ⟶ (eval n).obj Y := fun i => F.preimage ((eval n).map φ i)
    refine ⟨extend f, ?_⟩
    apply (eval (C:=D) n).map_injective
    funext i
    change F.map ((extend f).app i.castSucc i.succ (Fin.castSucc_le_succ i)) = _
    rw [extend_elementary]
    exact F.map_preimage _
noncomputable instance mapIsEquivalence (F : C ⥤ D) [F.Monoidal] [F.IsEquivalence] (n : ℕ) :
    (map (I:=Fin (n+1)) F).IsEquivalence where
noncomputable instance map₃IsEquivalence (F : C ⥤ D) [F.Braided] [F.IsEquivalence] (l m n : ℕ) :
    (map (I:=Fin (l+1)) (map (I:=Fin (m+1)) (map (I:=Fin (n+1)) F))).IsEquivalence :=
  inferInstance
end

section
open CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite

variable {C D : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
  [Groupoid.{0} D] [MonoidalCategory D] [SymmetricCategory D]
noncomputable def simplicialMap (F : C ⥤ D) [F.Monoidal] :
    simplicial (C:=C) ⟶ simplicial (C:=D) where
  app p := (map (I:=Fin (p.unop.len+1)) F).toCatHom
  naturality _ _ f := by
    apply Cat.ext
    exact reindex_map F f.unop.toOrderHom
noncomputable def bar : SSet := SimplicialDiagonal.nerveDiagonal.obj (simplicial (C:=C))
noncomputable def barMap (F : C ⥤ D) [F.Monoidal] : bar (C:=C) ⟶ bar (C:=D) :=
  SimplicialDiagonal.nerveDiagonal.map (simplicialMap F)
omit [SymmetricCategory C] [SymmetricCategory D] in
lemma barMap_homology_isIso (F : C ⥤ D) [F.Monoidal] [F.IsEquivalence] (n : ℕ) :
    IsIso (SSet.homologyMap (barMap F) DiagonalResolution.Z n) := by
  apply SimplicialDiagonal.nerveDiagonal_isIso
  intro p
  exact mapIsEquivalence F p.unop.len
end

end IntervalBar.Diagram

section
open CategoryTheory SimplicialObject Simplicial Opposite MonoidalCategory
namespace SimplicialDiagonal

noncomputable def fromZero (X : I ⥤ SSet) : X.obj (op ⦋0⦌) ⟶ diagonal.obj X where
  app n := (X.map (SimplexCategory.const n.unop ⦋0⦌ 0).op).app n
  naturality n m f := by
    change (X.obj (op ⦋0⦌)).map f ≫ (X.map _).app m =
      (X.map _).app n ≫ ((X.map f).app n ≫ (X.obj m).map f)
    rw [←Category.assoc,←NatTrans.comp_app,←X.map_comp]
    have hc : (SimplexCategory.const n.unop ⦋0⦌ 0).op ≫ f =
        (SimplexCategory.const m.unop ⦋0⦌ 0).op := Subsingleton.elim _ _
    rw [hc]
    exact (X.map (SimplexCategory.const m.unop ⦋0⦌ 0).op).naturality f
lemma fromZero_zero (X : I ⥤ SSet) (x : (X.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    (fromZero X).app (op ⦋0⦌) x=x := by
  change (X.map _).app _ x=x
  rw [Subsingleton.elim (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op (𝟙 _)]
  simp
instance diagonal_connected (X : I ⥤ SSet) [(X.obj (op ⦋0⦌)).IsConnected] :
    (diagonal.obj X).IsConnected where
  allEq u v := by
    obtain ⟨x,rfl⟩ := SSet.π₀.mk_surjective u
    obtain ⟨y,rfl⟩ := SSet.π₀.mk_surjective v
    have h := congrArg (SSet.mapπ₀ (fromZero X))
      (Subsingleton.elim (SSet.π₀.mk (X:=X.obj (op ⦋0⦌)) x) (SSet.π₀.mk y))
    erw [SSet.mapπ₀_mk, SSet.mapπ₀_mk, fromZero_zero, fromZero_zero] at h
    exact h
  nonempty := inferInstanceAs (Nonempty ((X.obj (op ⦋0⦌)).obj (op ⦋0⦌)))
end SimplicialDiagonal
namespace CategoryTheory.nerve
open scoped _root_.CategoryTheory _root_.CategoryTheory.nerve
lemma connected_of_hom {C : Type} [_root_.CategoryTheory.Category C] [Nonempty C]
    (h : ∀ x y : C,Nonempty (x ⟶ y)) : (_root_.CategoryTheory.nerve C).IsConnected where
  allEq u v := by
    obtain ⟨x,rfl⟩ := SSet.π₀.mk_surjective u
    obtain ⟨y,rfl⟩ := SSet.π₀.mk_surjective v
    exact SSet.π₀.sound (_root_.CategoryTheory.nerve.homEquiv.symm (Classical.choice (h (_root_.CategoryTheory.nerveEquiv x) (_root_.CategoryTheory.nerveEquiv y))))
  nonempty := ⟨nerveEquiv.symm (Classical.arbitrary C)⟩
end CategoryTheory.nerve
namespace IntervalBar.Diagram
variable (C : Type) [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable instance zero_nonempty : Nonempty (Diagram C (Fin 1)) := ⟨constantUnit⟩
noncomputable def zeroHom (X Y : Diagram C (Fin 1)) : X ⟶ Y :=
  (eval 0).preimage (fun i => Fin.elim0 i)
instance zero_nerve_connected : (nerve (Diagram C (Fin 1))).IsConnected :=
  _root_.OAI.CategoryTheory.nerve.connected_of_hom (fun X Y => ⟨zeroHom C X Y⟩)
instance bar_connected : (bar (C:=C)).IsConnected := by
  let X := (((Functor.whiskeringRight SimplicialDiagonal.I Cat SSet).obj nerveFunctor).obj (simplicial (C:=C)))
  have : (X.obj (op ⦋0⦌)).IsConnected := zero_nerve_connected C
  exact SimplicialDiagonal.diagonal_connected X
end IntervalBar.Diagram

end

open _root_.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
variable {D : Type} [Groupoid.{0} D] [MonoidalCategory D] [SymmetricCategory D]
variable {I J K : Type} [Preorder I] [Preorder J] [Preorder K]
lemma simplicialMap_reindex_id :
    simplicialMap (reindex (C:=C) (OrderHom.id (α:=I)))=𝟙 _ := by
  apply NatTrans.ext
  funext p
  apply Cat.ext
  exact map_reindex_id
lemma simplicialMap_reindex_comp (f : I →o J) (g : J →o K) :
    simplicialMap (reindex (C:=C) (g.comp f)) =
      simplicialMap (reindex g) ≫ simplicialMap (reindex f) := by
  apply NatTrans.ext
  funext p
  apply Cat.ext
  exact map_reindex_comp f g
@[simp] lemma barMap_reindex_id :
    barMap (reindex (C:=C) (OrderHom.id (α:=I)))=𝟙 _ := by
  simp [barMap,simplicialMap_reindex_id,bar]
lemma barMap_reindex_comp (f : I →o J) (g : J →o K) :
    barMap (reindex (C:=C) (g.comp f)) =
      barMap (reindex g) ≫ barMap (reindex f) := by
  simp [barMap,simplicialMap_reindex_comp]
  rfl
noncomputable def rows₂ : SimplexCategoryᵒᵖ ⥤ SSet where
  obj p := bar (C:=Diagram C (Fin (p.unop.len+1)))
  map f := barMap (reindex f.unop.toOrderHom)
  map_id _ := barMap_reindex_id
  map_comp f g := barMap_reindex_comp g.unop.toOrderHom f.unop.toOrderHom
noncomputable def bar₂ : SSet := SimplicialDiagonal.diagonal.obj (rows₂ (C:=C))
instance bar₂_connected : (bar₂ (C:=C)).IsConnected := by
  have : ((rows₂ (C:=C)).obj (op ⦋0⦌)).IsConnected := bar_connected _
  exact SimplicialDiagonal.diagonal_connected (rows₂ (C:=C))
lemma map_map_reindex (F : C ⥤ D) [F.Braided] (f : I →o J) :
    map (I:=K) (map (I:=J) F) ⋙ map (reindex f) =
      map (reindex f) ⋙ map (map (I:=I) F) := by
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq ?_ ?_ ?_
    · rfl
    · apply heq_of_eq
      funext k
      apply Iso.ext
      apply Hom.ext
      intro i j h
      change (((map F).map (A.unit k).hom ≫ Functor.OplaxMonoidal.η (map F)).app
          (f i) (f j) (f.monotone h)) ≫ 𝟙 _ =
        ((map F).map ((reindex f).map (A.unit k).hom ≫ Functor.OplaxMonoidal.η (reindex f)) ≫
          Functor.OplaxMonoidal.η (map F)).app i j h
      erw [comp_app, map_η_app (I:=J) F, comp_app, map_η_app (I:=I) F]
      change (F.map ((A.unit k).hom.app (f i) (f j) _) ≫ Functor.OplaxMonoidal.η F) ≫ 𝟙 _ =
        F.map ((A.unit k).hom.app (f i) (f j) _ ≫ 𝟙 _) ≫ Functor.OplaxMonoidal.η F
      erw [Category.comp_id, Category.comp_id]
    · apply heq_of_eq
      funext i j k hij hjk
      apply Iso.ext
      apply Hom.ext
      intro l m h
      change 𝟙 _ ≫ (Functor.LaxMonoidal.μ F _ _ ≫ F.map ((A.cut i j k hij hjk).hom.app (f l) (f m) _)) =
        Functor.LaxMonoidal.μ F _ _ ≫ F.map (𝟙 _ ≫ (A.cut i j k hij hjk).hom.app (f l) (f m) _)
      erw [Category.id_comp, Category.id_comp]
  · intro A B g
    apply Hom.ext; intro i j h
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    apply Hom.ext; intro l m hlm
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    simp only [map,reindex]
    erw [Category.id_comp, Category.comp_id]
    rfl
end IntervalBar.Diagram

end OAI
