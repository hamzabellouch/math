import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.PolygonPositionalMonoidal

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section PolygonStringGroupoid

open Classical CategoryTheory
open scoped MonoidalCategory
namespace PolygonObject
variable {a : ℕ}

abbrev RawString (a n : ℕ) := Fin (n+1) ⥤ PolygonObject a

def ladderProperty (a n : ℕ) : MorphismProperty (RawString a n) :=
  (positionalProperty a).functorCategory (Fin (n+1))

instance ladderProperty_multiplicative (n : ℕ) : (ladderProperty a n).IsMultiplicative where
  id_mem F i := identity_positional (F.obj i)
  comp_mem _ _ hf hg i := positional_comp (hf i) (hg i)

instance ladderProperty_monoidal (n : ℕ) : (ladderProperty a n).IsMonoidalStable where
  whiskerLeft F _ _ _ hg i := sumArrow_positional (identity_positional (F.obj i)) (hg i)
  whiskerRight _ hf G i := sumArrow_positional (hf i) (identity_positional (G.obj i))
  associator_hom_mem F G H i := sumAssoc_positional (F.obj i) (G.obj i) (H.obj i)
  associator_inv_mem F G H i := positional_inv (sumAssoc_positional (F.obj i) (G.obj i) (H.obj i))
  leftUnitor_hom_mem F i := leftUnit_positional (F.obj i)
  leftUnitor_inv_mem F i := positional_inv (leftUnit_positional (F.obj i))
  rightUnitor_hom_mem F i := rightUnit_positional (F.obj i)
  rightUnitor_inv_mem F i := positional_inv (rightUnit_positional (F.obj i))

instance ladderProperty_braided (n : ℕ) : (ladderProperty a n).IsStableUnderBraiding where
  braiding_hom_mem F G i := sumSwap_positional (F.obj i) (G.obj i)
  braiding_inv_mem F G i := positional_inv (sumSwap_positional (F.obj i) (G.obj i))

abbrev StringGroupoid (a n : ℕ) := WideSubcategory (ladderProperty a n)

noncomputable instance stringGroupoid_isIso {n : ℕ} (F G : StringGroupoid a n) (f : F ⟶ G) : IsIso f := by
  let : IsIso f.hom := NatIso.isIso_of_isIso_app f.hom
  refine ⟨⟨⟨CategoryTheory.inv f.hom,?_⟩,?_,?_⟩⟩
  · intro i
    rw [NatIso.isIso_inv_app]
    exact positional_inv (f.property i)
  · apply WideSubcategory.hom_ext
    exact IsIso.hom_inv_id f.hom
  · apply WideSubcategory.hom_ext
    exact IsIso.inv_hom_id f.hom

noncomputable instance stringGroupoid (n : ℕ) : Groupoid (StringGroupoid a n) :=
  Groupoid.ofIsIso (fun _ => inferInstance)

noncomputable def stringReindex {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) :
    StringGroupoid a m ⥤ StringGroupoid a n where
  obj F := ⟨u ⋙ F.obj⟩
  map f := ⟨CategoryTheory.Functor.whiskerLeft u f.hom,fun i => f.property (u.obj i)⟩
  map_id F := by apply WideSubcategory.hom_ext; rfl
  map_comp f g := by apply WideSubcategory.hom_ext; rfl

@[simp] theorem stringReindex_id (n : ℕ) : stringReindex (a:=a) (𝟭 (Fin (n+1)))=𝟭 _ := by
  apply CategoryTheory.Functor.ext
  · intro F G f; rfl
  · intro F; cases F; rfl

@[simp] theorem stringReindex_comp {n m k : ℕ}
    (u : Fin (n+1) ⥤ Fin (m+1)) (v : Fin (m+1) ⥤ Fin (k+1)) :
    stringReindex (a:=a) (u⋙v)=stringReindex v ⋙ stringReindex u := by
  apply CategoryTheory.Functor.ext
  · intro F G f; rfl
  · intro F; rfl

noncomputable instance stringReindex_monoidal {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) :
    (stringReindex (a:=a) u).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso := fun _ _ => Iso.refl _
    μIso_hom_natural_left := by intros; simp; apply WideSubcategory.hom_ext; rfl
    μIso_hom_natural_right := by intros; simp; apply WideSubcategory.hom_ext; rfl
    associativity := by
      intro first second third
      apply WideSubcategory.hom_ext
      apply NatTrans.ext
      funext point
      change (𝟙 _ ▷ _ ≫ 𝟙 _ ≫ (α_ _ _ _).hom) =
        ((α_ _ _ _).hom ≫ _ ◁ 𝟙 _ ≫ 𝟙 _)
      simp
    left_unitality := by
      intro object
      apply WideSubcategory.hom_ext
      apply NatTrans.ext
      funext point
      change (λ_ _).hom = 𝟙 _ ▷ _ ≫ 𝟙 _ ≫ (λ_ _).hom
      simp
    right_unitality := by
      intro object
      apply WideSubcategory.hom_ext
      apply NatTrans.ext
      funext point
      change (ρ_ _).hom = _ ◁ 𝟙 _ ≫ 𝟙 _ ≫ (ρ_ _).hom
      simp }

end PolygonObject
end PolygonStringGroupoid

open Classical CategoryTheory
namespace PolygonObject
variable {a n : ℕ}

def baseArrow (F : RawString a n) (i : Fin (n+1)) : F.obj 0 ⟶ F.obj i :=
  F.map (homOfLE (Fin.zero_le i))

@[simp] theorem baseArrow_zero (F : RawString a n) : baseArrow F 0=𝟙 _ := by
  unfold baseArrow
  exact (congrArg F.map (show homOfLE (Fin.zero_le (0 : Fin (n+1)))=𝟙 (0 : Fin (n+1))
    from Subsingleton.elim _ _)).trans (F.map_id _)

@[simp, reassoc] theorem baseArrow_comp (F : RawString a n) {i j : Fin (n+1)}
    (f : i ⟶ j) : baseArrow F i ≫ F.map f=baseArrow F j := by
  rw [baseArrow,←F.map_comp]
  congr 1

noncomputable def extendLadder {F G : RawString a n} (h : F.obj 0 ⟶ G.obj 0) : F ⟶ G where
  app i := CategoryTheory.inv (baseArrow F i) ≫ h ≫ baseArrow G i
  naturality i j f := by
    have he : F.map f ≫ CategoryTheory.inv (baseArrow F j)=CategoryTheory.inv (baseArrow F i) := by
      apply (cancel_epi (baseArrow F i)).mp
      rw [←Category.assoc,baseArrow_comp]
      simp
    simp only [←Category.assoc,he]
    simp only [Category.assoc,baseArrow_comp]

@[simp] theorem extendLadder_zero {F G : RawString a n} (h : F.obj 0 ⟶ G.obj 0) :
    (extendLadder h).app 0=h := by
  simp [extendLadder]

theorem ladder_ext {F G : RawString a n} {h k : F ⟶ G}
    (h0 : h.app 0=k.app 0) : h=k := by
  apply NatTrans.ext
  funext i
  apply (cancel_epi (baseArrow F i)).mp
  rw [show baseArrow F i=F.map (homOfLE (Fin.zero_le i)) from rfl,
    h.naturality,k.naturality,h0]

@[simp] theorem extendLadder_app_zero {F G : RawString a n} (h : F ⟶ G) :
    extendLadder (h.app 0)=h := ladder_ext (extendLadder_zero _)

def trajectory (F : RawString a n) (x : (F.obj 0).Point) (i : Fin (n+1)) :=
  ((baseArrow F i).toEquiv x).val.2

theorem ladder_preserves_trajectory {F G : StringGroupoid a n} (h : F ⟶ G)
    (x : (F.obj.obj 0).Point) :
    trajectory G.obj ((h.hom.app 0).toEquiv x)=trajectory F.obj x := by
  funext i
  have he := congrArg (fun k : F.obj.obj 0 ⟶ G.obj.obj i => k.toEquiv x)
    (h.hom.naturality (homOfLE (Fin.zero_le i)))
  change (h.hom.app i).toEquiv ((baseArrow F.obj i).toEquiv x) =
    (baseArrow G.obj i).toEquiv ((h.hom.app 0).toEquiv x) at he
  unfold trajectory
  rw [←he]
  exact h.property i _

theorem extendLadder_positional {F G : RawString a n} (h : F.obj 0 ⟶ G.obj 0)
    (he : ∀x,trajectory G (h.toEquiv x)=trajectory F x) :
    (ladderProperty a n) (extendLadder h) := by
  intro i y
  let x := (baseArrow F i).toEquiv.symm y
  have hi := congrFun (he x) i
  change ((baseArrow G i).toEquiv (h.toEquiv x)).val.2=
    ((baseArrow F i).toEquiv x).val.2 at hi
  simpa only [extendLadder,arrow_comp_apply,inv_arrow_apply,x,Equiv.apply_symm_apply] using hi

noncomputable def ladderEquiv (F G : StringGroupoid a n) :
    (F ⟶ G) ≃ {h : F.obj.obj 0 ⟶ G.obj.obj 0 //
      ∀x,trajectory G.obj (h.toEquiv x)=trajectory F.obj x} where
  toFun h := ⟨h.hom.app 0,ladder_preserves_trajectory h⟩
  invFun h := ⟨extendLadder h.val,extendLadder_positional h.val h.property⟩
  left_inv h := by apply WideSubcategory.hom_ext; exact extendLadder_app_zero h.hom
  right_inv h := by apply Subtype.ext; exact extendLadder_zero h.val

end PolygonObject

end SimpleAmenable

end OAI
