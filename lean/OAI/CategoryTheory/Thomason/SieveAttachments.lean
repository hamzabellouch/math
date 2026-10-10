import Mathlib
import OAI.CategoryTheory.Thomason.PartialPrisms
import OAI.CategoryTheory.Thomason.SimplexColimits

namespace OAI

/-! Sieve Attachments. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.OneCat
def liftInterval : Fin 2 →o Interval.{u} where
  toFun := ULift.up
  monotone' _ _ h := h

def cylinderMap {C D : Cat.{u,u}} (H : Cat.of (Interval.{u} × C) ⟶ D) :
    nerve C ⊗ Δ[1] ⟶ nerve D where
  app m := ↾fun x =>
    ((SSet.stdSimplex.objEquiv x.2).toOrderHom.toFunctor ⋙
      liftInterval.toFunctor).prod' x.1 ⋙ H.toFunctor
  naturality m n f := by
    apply ConcreteCategory.hom_ext
    intro x
    rfl

lemma cylinderMap_zero {C D : Cat.{u,u}} (H : Cat.of (Interval.{u} × C) ⟶ D) :
    SSet.ι₀ ≫ cylinderMap H = nerveFunctor.map (endpoint C 0 ≫ H) := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  rfl
lemma cylinderMap_one {C D : Cat.{u,u}} (H : Cat.of (Interval.{u} × C) ⟶ D) :
    SSet.ι₁ ≫ cylinderMap H = nerveFunctor.map (endpoint C 1 ≫ H) := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro x
  rfl

def homotopy {C D : Cat.{u,u}} (H : Cat.of (Interval.{u} × C) ⟶ D) :
    SSet.Homotopy (nerveFunctor.map (endpoint C 0 ≫ H))
      (nerveFunctor.map (endpoint C 1 ≫ H)) where
  h := cylinderMap H
  h₀ := cylinderMap_zero H
  h₁ := cylinderMap_one H
  rel := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x,hx⟩,θ⟩
    exact False.elim hx
end Thomason.OneCat

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.OneCat
variable {P : Type u} [PartialOrder P] (A : Set P) (r : P →o A)
    (hr : ∀ a : A, r a.val = a)
    (hadj : ∀ (a : A) (e : P), a.val ≤ e ↔ a ≤ r e)

include hadj in
lemma retract_le (e : P) : (r e).val ≤ e := (hadj (r e) e).mpr le_rfl

def orderCylinder : Interval.{u} × P →o P where
  toFun x := if x.1.down = 0 then (r x.2).val else x.2
  monotone' := by
    rintro ⟨⟨b⟩,e⟩ ⟨⟨c⟩,f⟩ ⟨hbc,hef⟩
    fin_cases b <;> fin_cases c
    · exact r.monotone hef
    · exact (retract_le A r hadj e).trans hef
    · simp at hbc
    · exact hef

def posetCylinder : Cat.of (Interval.{u} × P) ⟶ Cat.of P :=
  ({ obj := orderCylinder A r hadj
     map := fun f => homOfLE ((orderCylinder A r hadj).monotone
       ⟨leOfHom f.1,leOfHom f.2⟩) } : Interval.{u} × P ⥤ P).toCatHom

lemma posetCylinder_zero : endpoint (Cat.of P) 0 ≫ posetCylinder (P := P) A r hadj =
    r.toFunctor.toCatHom ≫ (OrderEmbedding.subtype A).toOrderHom.toFunctor.toCatHom := by
  apply Cat.Hom.ext
  exact CategoryTheory.Functor.ext (fun _ => rfl)
lemma posetCylinder_one : endpoint (Cat.of P) 1 ≫ posetCylinder (P := P) A r hadj = 𝟙 (Cat.of P) := by
  apply Cat.Hom.ext
  exact CategoryTheory.Functor.ext (fun _ => rfl)
include hr in
lemma posetCylinder_stationary :
    cylinder.map ((OrderEmbedding.subtype A).toOrderHom.toFunctor.toCatHom) ≫
      posetCylinder (P := P) A r hadj = projection (Cat.of A) ≫
        (OrderEmbedding.subtype A).toOrderHom.toFunctor.toCatHom := by
  apply Cat.Hom.ext
  exact CategoryTheory.Functor.ext (fun ⟨⟨b⟩,a⟩ => by
    change (if b = 0 then (r a.val).val else a.val) = a.val
    rw [hr a]
    simp)
include hr in
lemma posetRetraction : (OrderEmbedding.subtype A).toOrderHom.toFunctor.toCatHom ≫
    r.toFunctor.toCatHom = 𝟙 (Cat.of A) := by
  apply Cat.Hom.ext
  exact CategoryTheory.Functor.ext hr
end Thomason.OneCat

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.OneCat
open OmegaCategory

def nerveOfCategoryIso (C : Cat.{u,u}) : nerve C ≅ streetNerve (ofCategory C) :=
  nerveFunctor.mapIso (categorySkeletonIso C) ≪≫ (oneNerveIso (ofCategory_truncated C)).symm

instance oneUnitCatIso (C : Cat.{u,u}) :
    IsIso ((categorificationFiniteAdjunction 1).unit.app (nerveFunctor.obj C)) :=
  (categorificationFiniteAdjunction 1).isIso_unit_app_of_iso
    (X := ⟨ofCategory C,ofCategory_truncated C⟩) (nerveOfCategoryIso C)

def categorificationCatIso (C : Cat.{u,u}) : C ≅
    oneSkeletonCatFunctor.obj ((categorificationFinite 1).obj (nerveFunctor.obj C)) :=
  nerveFunctor.preimageIso (asIso ((categorificationFiniteAdjunction 1).unit.app (nerveFunctor.obj C)) ≪≫
    oneNerveIso ((categorificationFinite 1).obj (nerveFunctor.obj C)).property)

lemma categorificationCatIso_nerve (C : Cat.{u,u}) :
    nerveFunctor.map (categorificationCatIso C).hom =
      (categorificationFiniteAdjunction 1).unit.app (nerveFunctor.obj C) ≫
        (oneNerveIso ((categorificationFinite 1).obj (nerveFunctor.obj C)).property).hom := by
  exact nerveFunctor.map_preimage _

lemma categorificationCatIso_natural {C D : Cat.{u,u}} (f : C ⟶ D) :
    f ≫ (categorificationCatIso D).hom = (categorificationCatIso C).hom ≫
      oneSkeletonCatFunctor.map ((categorificationFinite 1).map (nerveFunctor.map f)) := by
  apply nerveFunctor.map_injective
  simp only [CategoryTheory.Functor.map_comp, categorificationCatIso_nerve]
  have hu := (categorificationFiniteAdjunction 1).unit.naturality (nerveFunctor.map f)
  change nerveFunctor.map f ≫ _ = _ at hu
  erw [← Category.assoc, hu]
  have h := oneNerveIso_natural
    ((categorificationFinite 1).obj (nerveFunctor.obj C)).property
    ((categorificationFinite 1).obj (nerveFunctor.obj D)).property
    ((categorificationFinite 1).map (nerveFunctor.map f))
  simp only [CategoryTheory.Functor.comp_map]
  exact congrArg ((categorificationFiniteAdjunction 1).unit.app (nerveFunctor.obj C) ≫ ·) h
end Thomason.OneCat

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.OneCat
open CategoryTheory Limits

lemma poset_pushout_nerve_weak {P : Type u} [PartialOrder P] (A : Set P)
    (r : P →o A) (hr : ∀ a : A, r a.val = a)
    (hadj : ∀ (a : A) (e : P), a.val ≤ e ↔ a ≤ r e)
    {X Y : Cat.{u,u}} {a : Cat.of A ⟶ X} {j : X ⟶ Y} {v : Cat.of P ⟶ Y}
    (sq : IsPushout a (OrderEmbedding.subtype A).toOrderHom.toFunctor.toCatHom j v) :
    simplicialWeakEquivalences (nerveFunctor.map j) := by
  obtain ⟨p,H,hp,h₀,h₁⟩ := pushout_deformation sq r.toFunctor.toCatHom
    (posetRetraction A r hr) (posetCylinder (P := P) A r hadj)
    (posetCylinder_zero A r hadj) (posetCylinder_one A r hadj)
    (posetCylinder_stationary A r hr hadj)
  have hh : SSet.Homotopy (nerveFunctor.map (p ≫ j)) (𝟙 (nerveFunctor.obj Y)) := by
    simpa only [h₀,h₁,CategoryTheory.Functor.map_id] using homotopy H
  have hw : simplicialWeakEquivalences (nerveFunctor.map (p ≫ j)) :=
    (simplicialWeakEquivalences_homotopy hh).mpr (simplicialWeakEquivalences.id_mem _)
  have rt : RetractArrow j (p ≫ j) :=
    { i := Arrow.homMk j (𝟙 Y) (by simp [← Category.assoc,hp])
      r := Arrow.homMk p (𝟙 Y) (by simp)
      retract := by ext <;> simp [hp] }
  exact simplicialWeakEquivalences.of_retract (rt.map nerveFunctor) hw
end Thomason.OneCat

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason
open CategoryTheory Limits OmegaCategory OneCat

theorem couniversalOne {P : Type u} [PartialOrder P] (A : Set P)
    (_hA : IsLowerSet A) (r : P →o A)
    (hr : ∀ a : A, r a.val = a)
    (hadj : ∀ (a : A) (e : P), a.val ≤ e ↔ a ≤ r e)
    (X : OmegaCategory.NCategory.{u} 1)
    (a : (categorificationFinite 1).obj (nerve A) ⟶ X) :
    simplicialWeakEquivalences ((streetNerveFinite 1).map
      (pushout.inl a ((categorificationFinite 1).map
        (nerveMap (OrderEmbedding.subtype A).toOrderHom.toFunctor)))) := by
  let inclusion : Cat.of A ⟶ Cat.of P := (OrderEmbedding.subtype A).toOrderHom.toFunctor.toCatHom
  let i := (categorificationFinite 1).map (nerveFunctor.map inclusion)
  let j := pushout.inl a i
  let v := pushout.inr a i
  let sk := oneSkeletonCatFunctor
  have sq := (IsPushout.of_hasPushout a i).map sk
  have sq' : IsPushout ((categorificationCatIso (Cat.of A)).hom ≫ sk.map a) inclusion
      (sk.map j) ((categorificationCatIso (Cat.of P)).hom ≫ sk.map v) := by
    apply sq.of_iso' (categorificationCatIso (Cat.of A)) (Iso.refl _)
      (categorificationCatIso (Cat.of P)) (Iso.refl _)
    · simp only [Iso.refl_hom, Category.comp_id]
      rfl
    · exact (categorificationCatIso_natural inclusion).symm
    · simp [j]
    · simp [v]
  have hw := poset_pushout_nerve_weak A r hr hadj sq'
  change simplicialWeakEquivalences ((streetNerveFinite 1).map j)
  apply simplicialWeakEquivalences.of_postcomp _
    (oneNerveFunctorIso.hom.app (pushout a i)) (simplicialWeakEquivalences.of_isIso _)
  rw [oneNerveFunctorIso.hom.naturality j]
  exact simplicialWeakEquivalences.comp_mem _ _
    (simplicialWeakEquivalences.of_isIso _) hw
end Thomason

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason
open CategoryTheory Limits OmegaCategory

theorem labelled_poset_attachment
    {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (g : Q →o P) (l : P →o Fin 2)
    {X Y : OmegaCategory.{u}} (ξ : X ⟶ interval) (η : Y ⟶ interval)
    (a : categorification.obj (nerve Q) ⟶ X) (h : X ⟶ Y)
    (i : categorification.obj (nerve P) ⟶ Y)
    (ha : a ≫ ξ = posetCategorificationLabel (l.comp g))
    (hh : h ≫ η = ξ) (hi : i ≫ η = posetCategorificationLabel l)
    (H : IsPushout a (categorification.map (nerveMap g.monotone.functor)) h i)
    (e : Fin 2) :
    IsPushout
      (posetCategorificationFiberMap (l.comp g) e ≫
        (fiberFunctor (intervalVertex e)).map (Over.homMk (U := Over.mk (posetCategorificationLabel (l.comp g))) (V := Over.mk ξ) a ha))
      (categorification.map (nerveMap (posetLevelMap g l e).monotone.functor))
      ((fiberFunctor (intervalVertex e)).map (Over.homMk (U := Over.mk ξ) (V := Over.mk η) h hh))
      (posetCategorificationFiberMap l e ≫
        (fiberFunctor (intervalVertex e)).map (Over.homMk (U := Over.mk (posetCategorificationLabel l)) (V := Over.mk η) i hi)) :=
by
  have hp := labelled_pushout_fibers
    (Over.homMk (U := Over.mk (posetCategorificationLabel (l.comp g))) (V := Over.mk ξ) a ha) (posetCategorificationOverMap g l)
    (Over.homMk (U := Over.mk ξ) (V := Over.mk η) h hh) (Over.homMk (U := Over.mk (posetCategorificationLabel l)) (V := Over.mk η) i hi) H e
  exact hp.of_iso' (posetCategorificationFiberIso (l.comp g) e)
    (Iso.refl _) (posetCategorificationFiberIso l e) (Iso.refl _)
    (by simp only [Iso.refl_hom, Category.comp_id]; rfl)
    (posetCategorificationFiberMap_natural g l e).symm
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
    (by simp only [Iso.refl_hom, Category.comp_id]; rfl)
end Thomason

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason
open CategoryTheory Limits OmegaCategory
noncomputable def posetCategorificationFiniteLabel (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (l : P →o Fin 2) :
    (categorificationFinite n).obj (nerve P) ⟶ finiteInterval n hn :=
  ((truncationOverFunctor n hn).obj (Over.mk (posetCategorificationLabel l))).hom

theorem labelled_poset_finite_attachment (n : ℕ) (hn : 1 ≤ n)
    {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (g : Q →o P) (l : P →o Fin 2)
    {X Y : NCategory.{u} n} (ξ : X ⟶ finiteInterval n hn) (η : Y ⟶ finiteInterval n hn)
    (a : (categorificationFinite n).obj (nerve Q) ⟶ X) (h : X ⟶ Y)
    (i : (categorificationFinite n).obj (nerve P) ⟶ Y)
    (ha : a ≫ ξ = posetCategorificationFiniteLabel n hn (l.comp g))
    (hh : h ≫ η = ξ) (hi : i ≫ η = posetCategorificationFiniteLabel n hn l)
    (H : IsPushout a ((categorificationFinite n).map (nerveMap g.monotone.functor)) h i)
    (e : Fin 2) :
    IsPushout
      (posetCategorificationFiniteFiberMap n hn (l.comp g) e ≫
        (fiberFiniteFunctor n hn e).map (Over.homMk
          (U := Over.mk (posetCategorificationFiniteLabel n hn (l.comp g))) (V := Over.mk ξ) a ha))
      ((categorificationFinite n).map (nerveMap (posetLevelMap g l e).monotone.functor))
      ((fiberFiniteFunctor n hn e).map (Over.homMk (U := Over.mk ξ) (V := Over.mk η) h hh))
      (posetCategorificationFiniteFiberMap n hn l e ≫
        (fiberFiniteFunctor n hn e).map (Over.homMk
          (U := Over.mk (posetCategorificationFiniteLabel n hn l)) (V := Over.mk η) i hi)) :=
by
  let : IsIso (posetCategorificationFiniteFiberMap n hn (l.comp g) e) :=
    posetCategorificationFiniteFiberMap_isIso n hn (l.comp g) e
  let : IsIso (posetCategorificationFiniteFiberMap n hn l e) :=
    posetCategorificationFiniteFiberMap_isIso n hn l e
  have hp := labelled_pushout_finite_fibers n hn
    (Over.homMk (U := Over.mk (posetCategorificationFiniteLabel n hn (l.comp g))) (V := Over.mk ξ) a ha)
    ((truncationOverFunctor n hn).map (posetCategorificationOverMap g l))
    (Over.homMk (U := Over.mk ξ) (V := Over.mk η) h hh)
    (Over.homMk (U := Over.mk (posetCategorificationFiniteLabel n hn l)) (V := Over.mk η) i hi) H e
  let sourceIso := asIso (posetCategorificationFiniteFiberMap n hn (l.comp g) e)
  let targetIso := asIso (posetCategorificationFiniteFiberMap n hn l e)
  exact hp.of_iso' sourceIso (Iso.refl _) targetIso (Iso.refl _)
    (by simp only [Iso.refl_hom, Category.comp_id]; rfl)
    (posetCategorificationFiniteFiberMap_natural n hn g l e).symm
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
    (by simp only [Iso.refl_hom, Category.comp_id]; rfl)
end Thomason

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.OmegaCategory
open CategoryTheory Limits

def constantLabel (C : OmegaCategory.{u}) (e : Fin 2) : C ⟶ interval where
  map _ := (intervalVertex e).val
  map_source k _ := by cases k <;> rfl
  map_target k _ := by cases k <;> rfl
  map_comp k _ _ _ _ := by cases k <;> rfl

@[simp] lemma comp_constantLabel {C D : OmegaCategory.{u}} (f : C ⟶ D) (e : Fin 2) :
    f ≫ constantLabel D e = constantLabel C e := rfl

def constantFiberIso (C : OmegaCategory.{u}) (e : Fin 2) :
    C ≅ ((constantLabel C e).fiber (intervalVertex e)).category where
  hom := ((constantLabel C e).fiber (intervalVertex e)).lift (𝟙 C) (fun _ => rfl)
  inv := ((constantLabel C e).fiber (intervalVertex e)).inclusion
  hom_inv_id := rfl
  inv_hom_id := rfl

lemma fiberInclusion_label {C : OmegaCategory.{u}} (q : C ⟶ interval) (e : Fin 2) :
    (q.fiber (intervalVertex e)).inclusion ≫ q =
      constantLabel (q.fiber (intervalVertex e)).category e := by
  apply Functor.ext
  funext x
  exact x.property

theorem endpoint_attachment {C X Y : OmegaCategory.{u}} (q : C ⟶ interval) (e : Fin 2)
    (a : (q.fiber (intervalVertex e)).category ⟶ X) (h : X ⟶ Y) (i : C ⟶ Y)
    (H : IsPushout a (q.fiber (intervalVertex e)).inclusion h i) :
    ∃ (η : Y ⟶ interval) (E : X ≅ (η.fiber (intervalVertex e)).category),
      E.hom ≫ (η.fiber (intervalVertex e)).inclusion = h := by
  let A := (q.fiber (intervalVertex e)).category
  let η : Y ⟶ interval := H.desc (constantLabel X e) q
    ((comp_constantLabel a e).trans (fiberInclusion_label q e).symm)
  have hh : h ≫ η = constantLabel X e := H.inl_desc _ _ _
  have hi : i ≫ η = q := H.inr_desc _ _ _
  let af : Over.mk (constantLabel A e) ⟶ Over.mk (constantLabel X e) :=
    Over.homMk a (comp_constantLabel a e)
  let gf : Over.mk (constantLabel A e) ⟶ Over.mk q :=
    Over.homMk (q.fiber (intervalVertex e)).inclusion (fiberInclusion_label q e)
  let hf : Over.mk (constantLabel X e) ⟶ Over.mk η := Over.homMk h hh
  let iF : Over.mk q ⟶ Over.mk η := Over.homMk i hi
  let F := fiberFunctor (intervalVertex e)
  have hp := labelled_pushout_fibers af gf hf iF H e
  let : IsIso (F.map gf) := (isoOfBijective (F.map gf) (by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact hxy
    · intro x
      exact ⟨⟨x,rfl⟩,rfl⟩)).isIso_hom
  let : IsIso (F.map hf) := hp.isIso_inl_of_isIso
  let fiberIso := asIso (F.map hf)
  let E : X ≅ (η.fiber (intervalVertex e)).category :=
    constantFiberIso X e ≪≫ fiberIso
  refine ⟨η,E,?_⟩
  rfl

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason
open CategoryTheory Limits OmegaCategory

def posetPieceFiberIso {P : Type u} [PartialOrder P] (S : Set P)
    (l : P →o Fin 2) (e : Fin 2) (hS : S = {p | l p = e}) :
    categorification.obj (nerve S) ≅
      ((posetCategorificationLabel l).fiber (intervalVertex e)).category := by
  subst S
  exact posetCategorificationFiberIso l e

lemma posetPieceFiberIso_inclusion {P : Type u} [PartialOrder P] (S : Set P)
    (l : P →o Fin 2) (e : Fin 2) (hS : S = {p | l p = e}) :
    (posetPieceFiberIso S l e hS).hom ≫
        ((posetCategorificationLabel l).fiber (intervalVertex e)).inclusion =
      categorification.map (nerveMap (OrderEmbedding.subtype S).toOrderHom.monotone.functor) := by
  subst S
  exact posetCategorificationFiberMap_inclusion l e

theorem poset_sieve_attachment {P : Type u} [PartialOrder P]
    (A : Set P) (hA : IsLowerSet A) {X Y : OmegaCategory.{u}}
    (a : categorification.obj (nerve A) ⟶ X) (h : X ⟶ Y)
    (i : categorification.obj (nerve P) ⟶ Y)
    (H : IsPushout a
      (categorification.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i) :
    ∃ S : Set Y.Objects, Y.IsObjectSieve S ∧
      ∃ e : X ≅ (Y.fullOn S).category, e.hom ≫ (Y.fullOn S).inclusion = h := by
  let l := NormalizedChains.PosetTables.lowerSegmentLabel A hA
  have hA' : A = {p | l p = 0} := by
    ext p
    exact (NormalizedChains.PosetTables.lowerSegmentLabel_zero A hA p).symm
  let E := posetPieceFiberIso A l 0 hA'
  have hp : IsPushout (E.inv ≫ a)
      ((posetCategorificationLabel l).fiber (intervalVertex 0)).inclusion h i :=
    H.of_iso E (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc])
      (by simp only [Iso.refl_hom, Category.comp_id]; exact (posetPieceFiberIso_inclusion A l 0 hA').symm)
      (by simp) (by simp)
  obtain ⟨η,F,hF⟩ := endpoint_attachment (posetCategorificationLabel l) 0 (E.inv ≫ a) h i hp
  refine ⟨intervalFiberObjects η 0, zero_fiber_isObjectSieve η,
    F ≪≫ intervalFiberFullIso η 0, ?_⟩
  exact hF

end Thomason

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.OmegaCategory
open CategoryTheory Limits

def constantFiniteFiberIso (n : ℕ) (hn : 1 ≤ n) (C : NCategory.{u} n) (e : Fin 2) :
    C ≅ (fiberFiniteFunctor n hn e).obj
      (Over.mk (X := finiteInterval n hn) (Y := C) (constantLabel C.val e)) where
  hom := (constantFiberIso C.val e).hom
  inv := (constantFiberIso C.val e).inv
  hom_inv_id := (constantFiberIso C.val e).hom_inv_id
  inv_hom_id := (constantFiberIso C.val e).inv_hom_id

theorem endpoint_finite_attachment (n : ℕ) (hn : 1 ≤ n)
    {C X Y : NCategory.{u} n} (q : C ⟶ finiteInterval n hn) (e : Fin 2)
    (a : (fiberFiniteFunctor n hn e).obj (Over.mk q) ⟶ X)
    (h : X ⟶ Y) (i : C ⟶ Y)
    (H : IsPushout a (fiberFiniteInclusion n hn e (Over.mk q)) h i) :
    ∃ (η : Y ⟶ finiteInterval n hn)
      (E : X ≅ (fiberFiniteFunctor n hn e).obj (Over.mk η)),
      E.hom ≫ fiberFiniteInclusion n hn e (Over.mk η) = h := by
  let F := fiberFiniteFunctor n hn e
  let A := F.obj (Over.mk q)
  let ξ : X ⟶ finiteInterval n hn := constantLabel X.val e
  let ξA : A ⟶ finiteInterval n hn := constantLabel A.val e
  let η : Y ⟶ finiteInterval n hn := H.desc ξ q
    ((comp_constantLabel a e).trans (fiberInclusion_label q e).symm)
  have hh : h ≫ η = ξ := H.inl_desc _ _ _
  have hi : i ≫ η = q := H.inr_desc _ _ _
  let af : Over.mk ξA ⟶ Over.mk ξ := Over.homMk a (comp_constantLabel a e)
  let gf : Over.mk ξA ⟶ Over.mk q :=
    Over.homMk (fiberFiniteInclusion n hn e (Over.mk q)) (fiberInclusion_label q e)
  let hf : Over.mk ξ ⟶ Over.mk η := Over.homMk h hh
  let iF : Over.mk q ⟶ Over.mk η := Over.homMk i hi
  have hp := labelled_pushout_finite_fibers n hn af gf hf iF H e
  let J := isoOfBijective ((nCategoryInclusion n).map (F.map gf)) (by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact hxy
    · intro x
      exact ⟨⟨x,rfl⟩,rfl⟩)
  let Jf : F.obj (Over.mk ξA) ≅ F.obj (Over.mk q) := {
    hom := J.hom, inv := J.inv, hom_inv_id := J.hom_inv_id, inv_hom_id := J.inv_hom_id }
  let : IsIso (F.map gf) := Jf.isIso_hom
  let : IsIso (F.map hf) := hp.isIso_inl_of_isIso
  let E : X ≅ F.obj (Over.mk η) := constantFiniteFiberIso n hn X e ≪≫ asIso (F.map hf)
  exact ⟨η,E,rfl⟩

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason
open CategoryTheory Limits OmegaCategory

def posetPieceFiniteFiberIso (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (S : Set P)
    (l : P →o Fin 2) (e : Fin 2) (hS : S = {p | l p = e}) :
    (categorificationFinite n).obj (nerve S) ≅
      (fiberFiniteFunctor n hn e).obj (Over.mk (posetCategorificationFiniteLabel n hn l)) := by
  subst S
  haveI := posetCategorificationFiniteFiberMap_isIso n hn l e
  let fiberIso := asIso (posetCategorificationFiniteFiberMap n hn l e)
  exact fiberIso

lemma posetPieceFiniteFiberIso_inclusion (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (S : Set P)
    (l : P →o Fin 2) (e : Fin 2) (hS : S = {p | l p = e}) :
    (posetPieceFiniteFiberIso n hn S l e hS).hom ≫
        fiberFiniteInclusion n hn e (Over.mk (posetCategorificationFiniteLabel n hn l)) =
      (categorificationFinite n).map (nerveMap (OrderEmbedding.subtype S).toOrderHom.monotone.functor) := by
  subst S
  exact posetCategorificationFiniteFiberMap_inclusion n hn l e

theorem poset_finite_sieve_attachment (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (A : Set P) (hA : IsLowerSet A)
    {X Y : NCategory.{u} n}
    (a : (categorificationFinite n).obj (nerve A) ⟶ X) (h : X ⟶ Y)
    (i : (categorificationFinite n).obj (nerve P) ⟶ Y)
    (H : IsPushout a
      ((categorificationFinite n).map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i) :
    ∃ S : Set Y.val.Objects, Y.val.IsObjectSieve S ∧
      ∃ e : X.val ≅ (Y.val.fullOn S).category,
        e.hom ≫ (Y.val.fullOn S).inclusion = h := by
  let l := NormalizedChains.PosetTables.lowerSegmentLabel A hA
  have hA' : A = {p | l p = 0} := by
    ext p
    exact (NormalizedChains.PosetTables.lowerSegmentLabel_zero A hA p).symm
  let E := posetPieceFiniteFiberIso n hn A l 0 hA'
  have hp : IsPushout (E.inv ≫ a)
      (fiberFiniteInclusion n hn 0 (Over.mk (posetCategorificationFiniteLabel n hn l))) h i :=
    H.of_iso E (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc])
      (by simp only [Iso.refl_hom, Category.comp_id]; exact (posetPieceFiniteFiberIso_inclusion n hn A l 0 hA').symm)
      (by simp) (by simp)
  obtain ⟨η,F,hF⟩ := endpoint_finite_attachment n hn
    (posetCategorificationFiniteLabel n hn l) 0 (E.inv ≫ a) h i hp
  refine ⟨intervalFiberObjects η 0, zero_fiber_isObjectSieve η,
    (nCategoryInclusion n).mapIso F ≪≫ intervalFiberFullIso η 0, ?_⟩
  exact hF

end Thomason

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.OmegaCategory
open CategoryTheory Limits
lemma Subcategory.inclusion_mono {C : OmegaCategory.{u}} (S : Subcategory C) :
    @Mono OmegaCategory.{u} inferInstance S.category C S.inclusion := by
  constructor
  intro Z f g he
  apply Functor.ext
  funext x
  apply Subtype.ext
  exact congrArg (fun F => F.map x) he
end Thomason.OmegaCategory

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory

def subposetMap {P : Type u} [PartialOrder P] (A S : Set P) (hAS : A ⊆ S) : A →o S :=
  ⟨fun x => ⟨x.val,hAS x.property⟩, fun _ _ h => h⟩

def IsPosetAttachmentPiece {P : Type u} [PartialOrder P]
    (A S : Set P) (hAS : A ⊆ S) {X Y : OmegaCategory.{u}}
    (a : categorification.obj (nerve A) ⟶ X) (h : X ⟶ Y)
    (i : categorification.obj (nerve P) ⟶ Y) (T : Set Y.Objects) : Prop :=
  ∃ (j : X ⟶ (Y.fullOn T).category)
    (k : categorification.obj (nerve S) ⟶ (Y.fullOn T).category),
    j ≫ (Y.fullOn T).inclusion = h ∧
    k ≫ (Y.fullOn T).inclusion = categorification.map
      (nerveMap (OrderEmbedding.subtype S).toOrderHom.monotone.functor) ≫ i ∧
    IsPushout a (categorification.map (nerveMap (subposetMap A S hAS).monotone.functor)) j k

def IsPosetNewPiece {P : Type u} [PartialOrder P]
    (S : Set P) {Y : OmegaCategory.{u}}
    (i : categorification.obj (nerve P) ⟶ Y) (T : Set Y.Objects) : Prop :=
  ∃ e : categorification.obj (nerve S) ≅ (Y.fullOn T).category,
    e.hom ≫ (Y.fullOn T).inclusion = categorification.map
      (nerveMap (OrderEmbedding.subtype S).toOrderHom.monotone.functor) ≫ i

open NormalizedChains.PosetTables

lemma posetLabel_constant {P : Type u} [PartialOrder P] (l : P →o Fin 2)
    (e : Fin 2) (hl : ∀ p, l p = e) :
    posetCategorificationLabel l = constantLabel (categorification.obj (nerve P)) e := by
  apply OmegaCategory.Functor.ext
  funext x
  apply ThinCell.ext <;> apply ULift.ext <;> exact hl _

variable {P : Type u} [PartialOrder P] (A : Set P)
    (l : P →o Fin 2) (b : Fin 2) (hlA : ∀ p : A, l p.val = b)
    {X Y : OmegaCategory.{u}} (a : categorification.obj (nerve A) ⟶ X)
    (h : X ⟶ Y) (i : categorification.obj (nerve P) ⟶ Y)
    (H : IsPushout a
      (categorification.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i)

def constantAttachmentLabel : Y ⟶ interval :=
  H.desc (constantLabel X b) (posetCategorificationLabel l) (by
    rw [comp_constantLabel, posetCategorificationLabel_natural]
    exact (posetLabel_constant _ b hlA).symm)

lemma constantAttachmentLabel_old :
    h ≫ constantAttachmentLabel A l b hlA a h i H = constantLabel X b := H.inl_desc _ _ _
lemma constantAttachmentLabel_new :
    i ≫ constantAttachmentLabel A l b hlA a h i H = posetCategorificationLabel l := H.inr_desc _ _ _

lemma subposetMap_comp (S : Set P) (hAS : A ⊆ S) :
    categorification.map (nerveMap (subposetMap A S hAS).monotone.functor) ≫
      categorification.map (nerveMap (OrderEmbedding.subtype S).toOrderHom.monotone.functor) =
    categorification.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor) := by
  rw [← categorification.map_comp]
  rfl

lemma constant_attachment_old_piece (S : Set P) (hAS : A ⊆ S)
    (hS : S = {p | l p = b}) :
    IsPosetAttachmentPiece A S hAS a h i
      (intervalFiberObjects (constantAttachmentLabel A l b hlA a h i H) b) := by
  let η := constantAttachmentLabel A l b hlA a h i H
  let q := posetCategorificationLabel l
  let C := categorification.obj (nerve A)
  let g : C ⟶ categorification.obj (nerve P) :=
    categorification.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)
  let src : Over interval := Over.mk (constantLabel C b)
  let old : Over interval := Over.mk (constantLabel X b)
  let af : src ⟶ old := Over.homMk a (comp_constantLabel a b)
  let gf : src ⟶ Over.mk q := Over.homMk g (by
    exact (posetCategorificationLabel_natural _ l).trans (posetLabel_constant _ b hlA))
  let hf : old ⟶ Over.mk η := Over.homMk h (constantAttachmentLabel_old A l b hlA a h i H)
  let if' : Over.mk q ⟶ Over.mk η := Over.homMk i (constantAttachmentLabel_new A l b hlA a h i H)
  let F := fiberFunctor (intervalVertex b)
  let E := posetPieceFiberIso S l b hS
  let j := (constantFiberIso X b).hom ≫ F.map hf
  let k := E.hom ≫ F.map if'
  have := (q.fiber (intervalVertex b)).inclusion_mono
  have hE := posetPieceFiberIso_inclusion S l b hS
  have hp : IsPushout a
      (categorification.map (nerveMap (subposetMap A S hAS).monotone.functor)) j k := by
    refine (labelled_pushout_fibers af gf hf if' H b).of_iso'
      (constantFiberIso C b) (constantFiberIso X b) E (Iso.refl _) ?_ ?_ ?_ ?_
    · rfl
    · apply (cancel_mono (C := OmegaCategory.{u})
        (q.fiber (intervalVertex b)).inclusion).mp
      change g = categorification.map (nerveMap (subposetMap A S hAS).monotone.functor) ≫
        (E.hom ≫ (q.fiber (intervalVertex b)).inclusion)
      rw [hE]
      exact (subposetMap_comp A S hAS).symm
    · simp only [Iso.refl_hom, Category.comp_id]; rfl
    · simp only [Iso.refl_hom, Category.comp_id]; rfl
  let Efull := intervalFiberFullIso η b
  refine ⟨j ≫ Efull.hom,k ≫ Efull.hom,?_,?_,?_⟩
  · rfl
  · change k ≫ (η.fiber (intervalVertex b)).inclusion = _
    change E.hom ≫ (F.map if' ≫ (η.fiber (intervalVertex b)).inclusion) = _
    change E.hom ≫ ((q.fiber (intervalVertex b)).inclusion ≫ i) = _
    rw [← Category.assoc, hE]
  · exact hp.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) Efull
      (by simp) (by simp) (by simp) (by simp)

lemma constant_attachment_new_piece (S : Set P) (e : Fin 2) (hbe : b ≠ e)
    (hS : S = {p | l p = e}) :
    IsPosetNewPiece S i (intervalFiberObjects (constantAttachmentLabel A l b hlA a h i H) e) := by
  let η := constantAttachmentLabel A l b hlA a h i H
  let q := posetCategorificationLabel l
  let C := categorification.obj (nerve A)
  let g : C ⟶ categorification.obj (nerve P) :=
    categorification.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)
  let src : Over interval := Over.mk (constantLabel C b)
  let old : Over interval := Over.mk (constantLabel X b)
  let af : src ⟶ old := Over.homMk a (comp_constantLabel a b)
  let gf : src ⟶ Over.mk q := Over.homMk g (by
    exact (posetCategorificationLabel_natural _ l).trans (posetLabel_constant _ b hlA))
  let hf : old ⟶ Over.mk η := Over.homMk h (constantAttachmentLabel_old A l b hlA a h i H)
  let if' : Over.mk q ⟶ Over.mk η := Over.homMk i (constantAttachmentLabel_new A l b hlA a h i H)
  let F := fiberFunctor (intervalVertex e)
  have : IsEmpty (F.obj src).Cell := ⟨fun x =>
    hbe (congrArg (fun c => c.left.down) x.property)⟩
  have : IsEmpty (F.obj old).Cell := ⟨fun x =>
    hbe (congrArg (fun c => c.left.down) x.property)⟩
  have : IsIso (F.map af) := isIso_of_isInitial
    (emptyOmegaIsInitial (F.obj src)) (emptyOmegaIsInitial (F.obj old)) _
  have hp := labelled_pushout_fibers af gf hf if' H e
  have : IsIso (F.map if') := hp.isIso_inr_of_isIso
  let E := posetPieceFiberIso S l e hS
  let fiberIso := asIso (F.map if')
  refine ⟨E ≪≫ fiberIso ≪≫ intervalFiberFullIso η e, ?_⟩
  change E.hom ≫ (F.map if' ≫ (η.fiber (intervalVertex e)).inclusion) = _
  change E.hom ≫ ((q.fiber (intervalVertex e)).inclusion ≫ i) = _
  rw [← Category.assoc, posetPieceFiberIso_inclusion]

end Thomason.Attachments

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory NormalizedChains.PosetTables

lemma tableLabel_objects {P : Type u} [PartialOrder P] (l : P →o Fin 2)
    (x : (NormalizedChains.complex P).nu.Objects) :
    (tableLabel l).objects x = intervalVertex (l (NormalizedChains.tableObjectsEquiv x)) := by
  apply Subtype.ext
  apply ThinCell.ext <;> apply ULift.ext
  · exact congrArg l (congrArg NormalizedChains.tableObjectsEquiv
      ((NormalizedChains.complex P).nu.sourceObject_object x))
  · exact congrArg l (congrArg NormalizedChains.tableObjectsEquiv
      ((NormalizedChains.complex P).nu.targetObject_object x))

lemma posetLabel_objects {P : Type u} [PartialOrder P] (l : P →o Fin 2)
    (x : (categorification.obj (nerve P)).Objects) :
    (posetCategorificationLabel l).objects x = intervalVertex
      (l (NormalizedChains.tableObjectsEquiv ((posetCategorificationTableMap P).objects x))) := by
  change (tableLabel l).objects ((posetCategorificationTableMap P).objects x) = _
  exact tableLabel_objects l _

lemma interval_vertex_mem_old {X Y : OmegaCategory.{u}} (h : X ⟶ Y)
    (η : Y ⟶ interval) (e : Fin 2) (he : h ≫ η = constantLabel X e) (x : X.Objects) :
    h.objects x ∈ intervalFiberObjects η e := by
  exact congrArg (fun f : X ⟶ interval => f.objects x) he

lemma interval_vertex_mem_new {P : Type u} [PartialOrder P] {Y : OmegaCategory.{u}}
    (i : categorification.obj (nerve P) ⟶ Y) (η : Y ⟶ interval) (l : P →o Fin 2)
    (hi : i ≫ η = posetCategorificationLabel l)
    (x : (categorification.obj (nerve P)).Objects) (e : Fin 2)
    (he : l (NormalizedChains.tableObjectsEquiv ((posetCategorificationTableMap P).objects x)) = e) :
    i.objects x ∈ intervalFiberObjects η e := by
  change η.objects (i.objects x) = intervalVertex e
  exact (congrArg (fun f : categorification.obj (nerve P) ⟶ interval => f.objects x) hi).trans
    ((posetLabel_objects l x).trans (congrArg intervalVertex he))

lemma labelled_objects_cover {P : Type u} [PartialOrder P] {A : Set P}
    {X Y : OmegaCategory.{u}} {a : categorification.obj (nerve A) ⟶ X}
    {h : X ⟶ Y} {i : categorification.obj (nerve P) ⟶ Y}
    (H : IsPushout a
      (categorification.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i)
    (η₁ η₂ : Y ⟶ interval) (l₁ l₂ : P →o Fin 2) (e : Fin 2)
    (hh : h ≫ η₁ = constantLabel X e ∨ h ≫ η₂ = constantLabel X e)
    (hi₁ : i ≫ η₁ = posetCategorificationLabel l₁)
    (hi₂ : i ≫ η₂ = posetCategorificationLabel l₂)
    (hl : ∀ p, l₁ p = e ∨ l₂ p = e) :
    intervalFiberObjects η₁ e ∪ intervalFiberObjects η₂ e = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  rcases Types.eq_or_eq_of_isPushout (H.map objectsFunctor) y with ⟨x,rfl⟩ | ⟨x,rfl⟩
  · rcases hh with hh | hh
    · exact Or.inl (interval_vertex_mem_old h η₁ e hh x)
    · exact Or.inr (interval_vertex_mem_old h η₂ e hh x)
  · rcases hl (NormalizedChains.tableObjectsEquiv ((posetCategorificationTableMap P).objects x)) with hx | hx
    · exact Or.inl (interval_vertex_mem_new i η₁ l₁ hi₁ x e hx)
    · exact Or.inr (interval_vertex_mem_new i η₂ l₂ hi₂ x e hx)

lemma maxLabel_objects_fiber {C : OmegaCategory.{u}} (p q : C ⟶ interval) :
    intervalFiberObjects (maxLabel p q) 0 =
      intervalFiberObjects p 0 ∩ intervalFiberObjects q 0 := by
  ext x
  change (maxLabel p q).objects x = intervalVertex 0 ↔
    p.objects x = intervalVertex 0 ∧ q.objects x = intervalVertex 0
  erw [← Subtype.val_inj,← Subtype.val_inj,← Subtype.val_inj]
  exact Set.ext_iff.mp (maxLabel_zero_fiber p q) x.val

lemma minLabel_objects_fiber {C : OmegaCategory.{u}} (p q : C ⟶ interval) :
    intervalFiberObjects (minLabel p q) 1 =
      intervalFiberObjects p 1 ∩ intervalFiberObjects q 1 := by
  ext x
  change (minLabel p q).objects x = intervalVertex 1 ↔
    p.objects x = intervalVertex 1 ∧ q.objects x = intervalVertex 1
  erw [← Subtype.val_inj,← Subtype.val_inj,← Subtype.val_inj]
  exact Set.ext_iff.mp (minLabel_one_fiber p q) x.val

lemma comp_maxLabel {C D : OmegaCategory.{u}} (f : C ⟶ D) (p q : D ⟶ interval) :
    f ≫ maxLabel p q = maxLabel (f ≫ p) (f ≫ q) := rfl
lemma comp_minLabel {C D : OmegaCategory.{u}} (f : C ⟶ D) (p q : D ⟶ interval) :
    f ≫ minLabel p q = minLabel (f ≫ p) (f ≫ q) := rfl

end Thomason.Attachments

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.Attachments
open CategoryTheory Limits OmegaCategory NormalizedChains.PosetTables

theorem sieve_attachment_covers {P : Type u} [PartialOrder P]
    (A S₁ S₂ : Set P) (h₁ : IsLowerSet S₁) (h₂ : IsLowerSet S₂)
    (hA₁ : A ⊆ S₁) (hA₂ : A ⊆ S₂) (hcover : S₁ ∪ S₂ = Set.univ)
    {X Y : OmegaCategory.{u}} (a : categorification.obj (nerve A) ⟶ X)
    (h : X ⟶ Y) (i : categorification.obj (nerve P) ⟶ Y)
    (H : IsPushout a
      (categorification.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i) :
    ∃ T₁ T₂ : Set Y.Objects,
      Y.IsObjectSieve T₁ ∧ Y.IsObjectSieve T₂ ∧ T₁ ∪ T₂ = Set.univ ∧
      IsPosetAttachmentPiece A S₁ hA₁ a h i T₁ ∧
      IsPosetAttachmentPiece A S₂ hA₂ a h i T₂ ∧
      IsPosetAttachmentPiece A (S₁ ∩ S₂) (fun _ hx => ⟨hA₁ hx,hA₂ hx⟩)
        a h i (T₁ ∩ T₂) :=
by
  classical
  let l₁ := lowerSegmentLabel S₁ h₁
  let l₂ := lowerSegmentLabel S₂ h₂
  let l₃ : P →o Fin 2 := ⟨fun p => max (l₁ p) (l₂ p),
    fun _ _ he => max_le_max (l₁.monotone he) (l₂.monotone he)⟩
  have hl₁ : ∀ p : A, l₁ p.val = 0 := fun p => (lowerSegmentLabel_zero S₁ h₁ _).mpr (hA₁ p.property)
  have hl₂ : ∀ p : A, l₂ p.val = 0 := fun p => (lowerSegmentLabel_zero S₂ h₂ _).mpr (hA₂ p.property)
  have hl₃ : ∀ p : A, l₃ p.val = 0 := by intro p; change max (l₁ p.val) (l₂ p.val) = 0; rw [hl₁,hl₂]; rfl
  have hS₁ : S₁ = {p | l₁ p = 0} := by ext p; exact (lowerSegmentLabel_zero S₁ h₁ p).symm
  have hS₂ : S₂ = {p | l₂ p = 0} := by ext p; exact (lowerSegmentLabel_zero S₂ h₂ p).symm
  have hS₃ : S₁ ∩ S₂ = {p | l₃ p = 0} := by
    ext p
    change (p ∈ S₁ ∧ p ∈ S₂) ↔
      max (if p ∈ S₁ then (0 : Fin 2) else 1) (if p ∈ S₂ then 0 else 1) = 0
    by_cases hp₁ : p ∈ S₁ <;> by_cases hp₂ : p ∈ S₂ <;>
      simp [hp₁,hp₂]
  let η₁ := constantAttachmentLabel A l₁ 0 hl₁ a h i H
  let η₂ := constantAttachmentLabel A l₂ 0 hl₂ a h i H
  let η₃ := constantAttachmentLabel A l₃ 0 hl₃ a h i H
  have hη₃ : η₃ = maxLabel η₁ η₂ := by
    apply H.hom_ext
    · change h ≫ constantAttachmentLabel A l₃ 0 hl₃ a h i H = _
      rw [constantAttachmentLabel_old,comp_maxLabel,
        constantAttachmentLabel_old,constantAttachmentLabel_old]
      rfl
    · change i ≫ constantAttachmentLabel A l₃ 0 hl₃ a h i H = _
      rw [constantAttachmentLabel_new,comp_maxLabel,
        constantAttachmentLabel_new,constantAttachmentLabel_new]
      rfl
  have hp₃ := constant_attachment_old_piece A l₃ 0 hl₃ a h i H
    (S₁ ∩ S₂) (fun _ hx => ⟨hA₁ hx,hA₂ hx⟩) hS₃
  change IsPosetAttachmentPiece A (S₁ ∩ S₂) _ a h i (intervalFiberObjects η₃ 0) at hp₃
  rw [hη₃,maxLabel_objects_fiber] at hp₃
  refine ⟨intervalFiberObjects η₁ 0,intervalFiberObjects η₂ 0,
    zero_fiber_isObjectSieve η₁,zero_fiber_isObjectSieve η₂,?_,
    constant_attachment_old_piece A l₁ 0 hl₁ a h i H S₁ hA₁ hS₁,
    constant_attachment_old_piece A l₂ 0 hl₂ a h i H S₂ hA₂ hS₂,hp₃⟩
  refine labelled_objects_cover H η₁ η₂ l₁ l₂ 0
    (Or.inl (constantAttachmentLabel_old A l₁ 0 hl₁ a h i H))
    (constantAttachmentLabel_new A l₁ 0 hl₁ a h i H)
    (constantAttachmentLabel_new A l₂ 0 hl₂ a h i H) ?_
  intro p
  have hp : p ∈ S₁ ∪ S₂ := by rw [hcover]; trivial
  exact hp.imp ((lowerSegmentLabel_zero S₁ h₁ p).mpr) ((lowerSegmentLabel_zero S₂ h₂ p).mpr)

end Thomason.Attachments

end

end OAI
