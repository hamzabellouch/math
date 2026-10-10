import Mathlib
import OAI.CategoryTheory.Thomason.Generators

namespace OAI

/-! Labelled Fibers. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

def opFiniteFunctor (n : ℕ) : CategoryTheory.Functor (NCategory.{u} n) (NCategory.{u} n) where
  obj C := ⟨C.val.op, op_truncated C.property⟩
  map F := Thomason.OmegaCategory.Functor.op F

def opFiniteEquivalence (n : ℕ) : NCategory.{u} n ≌ NCategory.{u} n where
  functor := opFiniteFunctor n
  inverse := opFiniteFunctor n
  unitIso := Iso.refl _
  counitIso := Iso.refl _

instance opFiniteFunctor_isEquivalence (n : ℕ) : (opFiniteFunctor.{u} n).IsEquivalence :=
  (opFiniteEquivalence n).isEquivalence_functor

def reverseLabelFiniteObj (n : ℕ) (hn : 1 ≤ n) (p : Over (finiteInterval.{u} n hn)) :
    Over (finiteInterval.{u} n hn) :=
  Over.mk (X := finiteInterval n hn) (Y := (opFiniteFunctor n).obj p.left)
    (reverseLabel p.hom)

def reverseLabelFiniteFunctor (n : ℕ) (hn : 1 ≤ n) :
    CategoryTheory.Functor (Over (finiteInterval.{u} n hn)) (Over (finiteInterval.{u} n hn)) where
  obj := reverseLabelFiniteObj n hn
  map {p q} F := Over.homMk
    (U := reverseLabelFiniteObj n hn p) (V := reverseLabelFiniteObj n hn q) (Thomason.OmegaCategory.Functor.op F.left) (by
      apply Functor.ext
      funext x
      have he := congrArg (fun f : Functor p.left.val interval => f.map x) (Over.w F)
      exact congrArg intervalReflect.map he)
  map_id p := by apply Over.OverMorphism.ext; rfl
  map_comp F G := by apply Over.OverMorphism.ext; rfl

def reverseLabelFiniteTwiceIso (n : ℕ) (hn : 1 ≤ n) :
    reverseLabelFiniteFunctor.{u} n hn ⋙ reverseLabelFiniteFunctor n hn ≅ 𝟭 _ :=
  NatIso.ofComponents (fun p => Over.isoMk (Iso.refl p.left) (by
    change p.hom = reverseLabel (reverseLabel p.hom)
    exact (reverseLabel_reverseLabel p.hom).symm)) (by
      intro p q F
      apply Over.OverMorphism.ext
      rfl)

def reverseLabelFiniteEquivalence (n : ℕ) (hn : 1 ≤ n) :
    Over (finiteInterval.{u} n hn) ≌ Over (finiteInterval.{u} n hn) where
  functor := reverseLabelFiniteFunctor n hn
  inverse := reverseLabelFiniteFunctor n hn
  unitIso := (reverseLabelFiniteTwiceIso n hn).symm
  counitIso := reverseLabelFiniteTwiceIso n hn
  functor_unitIso_comp p := by
    apply Over.OverMorphism.ext
    rfl

instance reverseLabelFiniteFunctor_isEquivalence (n : ℕ) (hn : 1 ≤ n) :
    (reverseLabelFiniteFunctor.{u} n hn).IsEquivalence :=
  (reverseLabelFiniteEquivalence n hn).isEquivalence_functor

def reversedZeroFiberFiniteIso (n : ℕ) (hn : 1 ≤ n) (p : Over (finiteInterval.{u} n hn)) :
    (opFiniteFunctor n).obj ((fiberFiniteFunctor n hn 0).obj
      ((reverseLabelFiniteFunctor n hn).obj p)) ≅ (fiberFiniteFunctor n hn 1).obj p where
  hom := {
    map := fun x => ⟨x.val, by
      apply intervalReflect_injective
      exact x.property⟩
    map_source := fun _ _ => rfl
    map_target := fun _ _ => rfl
    map_comp := fun _ _ _ _ _ => rfl }
  inv := {
    map := fun x => ⟨x.val, by
      change intervalReflect.map (p.hom.map x.val) = (intervalVertex 0).val
      rw [x.property]
      rfl⟩
    map_source := fun _ _ => rfl
    map_target := fun _ _ => rfl
    map_comp := fun _ _ _ _ _ => rfl }
  hom_inv_id := by apply Functor.ext; rfl
  inv_hom_id := by apply Functor.ext; rfl

def reversedZeroFiberFiniteNatIso (n : ℕ) (hn : 1 ≤ n) :
    (reverseLabelFiniteFunctor.{u} n hn ⋙ fiberFiniteFunctor n hn 0) ⋙ opFiniteFunctor n ≅
      fiberFiniteFunctor n hn 1 :=
  NatIso.ofComponents (reversedZeroFiberFiniteIso n hn) (by
    intro p q F
    apply Functor.ext
    rfl)

noncomputable instance oneFiberFinite_preservesColimits (n : ℕ) (hn : 1 ≤ n) :
    Limits.PreservesColimitsOfSize.{v,w} (fiberFiniteFunctor.{u} n hn 1) :=
  Limits.preservesColimits_of_natIso (reversedZeroFiberFiniteNatIso n hn)

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory Limits

lemma labelled_pushout_fibers {A B C D : Over interval.{u}}
    (f : A ⟶ B) (g : A ⟶ C) (h : B ⟶ D) (i : C ⟶ D)
    (H : IsPushout f.left g.left h.left i.left) (e : Fin 2) :
    IsPushout ((fiberFunctor (intervalVertex e)).map f)
      ((fiberFunctor (intervalVertex e)).map g)
      ((fiberFunctor (intervalVertex e)).map h)
      ((fiberFunctor (intervalVertex e)).map i) := by
  have hp : IsPushout f g h i := H.of_map_of_faithful (Over.forget interval)
  fin_cases e
  · exact hp.map (fiberFunctor (intervalVertex 0))
  · exact hp.map (fiberFunctor (intervalVertex 1))

lemma labelled_pushout_finite_fibers (n : ℕ) (hn : 1 ≤ n)
    {A B C D : Over (finiteInterval.{u} n hn)}
    (f : A ⟶ B) (g : A ⟶ C) (h : B ⟶ D) (i : C ⟶ D)
    (H : IsPushout f.left g.left h.left i.left) (e : Fin 2) :
    IsPushout ((fiberFiniteFunctor n hn e).map f)
      ((fiberFiniteFunctor n hn e).map g)
      ((fiberFiniteFunctor n hn e).map h)
      ((fiberFiniteFunctor n hn e).map i) := by
  have hp : IsPushout f g h i := H.of_map_of_faithful (Over.forget (finiteInterval n hn))
  fin_cases e
  · exact hp.map (fiberFiniteFunctor n hn 0)
  · exact hp.map (fiberFiniteFunctor n hn 1)

lemma pushout_objects {A B C D : OmegaCategory.{u}}
    (f : A ⟶ B) (g : A ⟶ C) (h : B ⟶ D) (i : C ⟶ D)
    (H : IsPushout f g h i) :
    IsPushout (objectsFunctor.map f) (objectsFunctor.map g)
      (objectsFunctor.map h) (objectsFunctor.map i) := H.map objectsFunctor

lemma pushout_finite_objects (n : ℕ) (hn : 1 ≤ n) {A B C D : NCategory.{u} n}
    (f : A ⟶ B) (g : A ⟶ C) (h : B ⟶ D) (i : C ⟶ D)
    (H : IsPushout f g h i) :
    IsPushout ((objectsFiniteFunctor n).map f) ((objectsFiniteFunctor n).map g)
      ((objectsFiniteFunctor n).map h) ((objectsFiniteFunctor n).map i) := by
  let : PreservesColimitsOfSize.{0,0} (objectsFiniteFunctor.{u} n) :=
    objectsFinite_preservesColimits n hn
  exact H.map _

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.Attachments

open CategoryTheory Limits

variable {P X : Type u} (A : Set P) (a : A → X)

noncomputable def complementMap (p : P) : X ⊕ {p : P // p ∉ A} := by
  classical
  exact if hp : p ∈ A then Sum.inl (a ⟨p,hp⟩) else Sum.inr ⟨p,hp⟩

lemma complementMap_old (p : A) : complementMap A a p.val = Sum.inl (a p) := by
  simp [complementMap, p.property]

lemma complementMap_new (p : {p : P // p ∉ A}) : complementMap A a p.val = Sum.inr p := by
  simp [complementMap, p.property]

noncomputable def complementCocone : PushoutCocone (TypeCat.ofHom a)
    (TypeCat.ofHom (Subtype.val : A → P)) :=
  PushoutCocone.mk (TypeCat.ofHom (Sum.inl : X → X ⊕ {p : P // p ∉ A}))
    (TypeCat.ofHom (complementMap A a)) (by
      apply ConcreteCategory.hom_ext
      exact fun p => (complementMap_old A a p).symm)

noncomputable def complementCoconeIsColimit : IsColimit (complementCocone A a) :=
  PushoutCocone.IsColimit.mk _
    (fun s => TypeCat.ofHom (Sum.elim s.inl (fun p => s.inr p.val)))
    (fun s => by apply ConcreteCategory.hom_ext; intro x; rfl)
    (fun s => by
      apply ConcreteCategory.hom_ext
      intro p
      by_cases hp : p ∈ A
      · change Sum.elim s.inl (fun p => s.inr p.val) (complementMap A a p) = s.inr p
        rw [show complementMap A a p = Sum.inl (a ⟨p,hp⟩) from complementMap_old A a ⟨p,hp⟩]
        exact congrArg (fun k : (↑A : Type u) ⟶ s.pt => k ⟨p,hp⟩) s.condition
      · change Sum.elim s.inl (fun p => s.inr p.val) (complementMap A a p) = s.inr p
        rw [show complementMap A a p = Sum.inr ⟨p,hp⟩ from complementMap_new A a ⟨p,hp⟩]
        rfl)
    (fun s m hl hr => by
      apply ConcreteCategory.hom_ext
      rintro (x | ⟨p,hp⟩)
      · exact congrArg (fun k : X ⟶ s.pt => k x) hl
      · have he := congrArg (fun k : P ⟶ s.pt => k p) hr
        change m (complementMap A a p) = s.inr p at he
        rwa [show complementMap A a p = Sum.inr ⟨p,hp⟩ from complementMap_new A a ⟨p,hp⟩] at he)

noncomputable def pushoutComplementIso {Y : Type u} (h : X ⟶ Y) (i : P ⟶ Y)
    (H : IsPushout (TypeCat.ofHom a) (TypeCat.ofHom (Subtype.val : A → P)) h i) :
    Y ≅ X ⊕ {p : P // p ∉ A} :=
  H.isColimit.coconePointUniqueUpToIso (complementCoconeIsColimit A a)

end Thomason.Attachments

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Limits OmegaCategory Simplicial

lemma posetCategorificationFiniteObjectsIso_natural (n : ℕ) (hn : 1 ≤ n)
    {P Q : Type u} [PartialOrder P] [PartialOrder Q] (f : P →o Q) :
    (objectsFiniteFunctor n).map ((categorificationFinite n).map (nerveMap f.monotone.functor)) ≫
        (posetCategorificationFiniteObjectsIso n hn Q).hom =
      (posetCategorificationFiniteObjectsIso n hn P).hom ≫ TypeCat.ofHom f := by
  dsimp only [posetCategorificationFiniteObjectsIso, Iso.trans_hom]
  generalize he : categorificationFiniteObjectsIso n hn = e
  exact congrArg (fun k : ((categorificationFinite n).obj (nerve P)).val.Objects ⟶ (nerve Q) _⦋0⦌ =>
    k ≫ nerveEquiv.toIso.hom) (e.hom.naturality (nerveMap f.monotone.functor))

lemma pushoutObjectCoordinateChange {Z X P Y A Q : Type u}
    (f : Z ⟶ X) (g : Z ⟶ P) (h : X ⟶ Y) (i : P ⟶ Y)
    (H : IsPushout f g h i) (e : Z ≅ A) (e' : P ≅ Q) (j : A ⟶ Q)
    (hj : g ≫ e'.hom = e.hom ≫ j) :
    IsPushout (e.inv ≫ f) j h (e'.inv ≫ i) := by
  exact H.of_iso e (Iso.refl _) e' (Iso.refl _)
    (by simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]) hj
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
    (by simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc])

lemma poset_pushout_objects {P : Type u} [PartialOrder P] (A : Set P)
    {X Y : OmegaCategory.{u}} (a : categorification.obj (nerve A) ⟶ X)
    (h : X ⟶ Y) (i : categorification.obj (nerve P) ⟶ Y)
    (H : IsPushout a (categorification.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i) :
    IsPushout ((posetCategorificationObjectsIso A).inv ≫ objectsFunctor.map a)
      (TypeCat.ofHom (Subtype.val : A → P)) (objectsFunctor.map h)
      ((posetCategorificationObjectsIso P).inv ≫ objectsFunctor.map i) := by
  exact pushoutObjectCoordinateChange _ _ _ _ (H.map objectsFunctor)
    (posetCategorificationObjectsIso A) (posetCategorificationObjectsIso P) _
    (by
      have he := posetCategorificationObjectsIso_natural (P := (↑A : Type u)) (Q := P)
        (OrderEmbedding.subtype A).toOrderHom
      rw [show TypeCat.ofHom (OrderEmbedding.subtype A).toOrderHom =
        TypeCat.ofHom (Subtype.val : A → P) from rfl] at he
      exact he)

noncomputable def posetPushoutObjectsComplementIso {P : Type u} [PartialOrder P] (A : Set P)
    {X Y : OmegaCategory.{u}} (a : categorification.obj (nerve A) ⟶ X)
    (h : X ⟶ Y) (i : categorification.obj (nerve P) ⟶ Y)
    (H : IsPushout a (categorification.map (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i) :
    Y.Objects ≅ X.Objects ⊕ {p : P // p ∉ A} :=
  Attachments.pushoutComplementIso A
    ((posetCategorificationObjectsIso A).inv ≫ objectsFunctor.map a)
    (objectsFunctor.map h) ((posetCategorificationObjectsIso P).inv ≫ objectsFunctor.map i)
    (poset_pushout_objects A a h i H)

lemma poset_pushout_finite_objects (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (A : Set P)
    {X Y : NCategory.{u} n} (a : (categorificationFinite n).obj (nerve A) ⟶ X)
    (h : X ⟶ Y) (i : (categorificationFinite n).obj (nerve P) ⟶ Y)
    (H : IsPushout a ((categorificationFinite n).map
      (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i) :
    IsPushout ((posetCategorificationFiniteObjectsIso n hn A).inv ≫ (objectsFiniteFunctor n).map a)
      (TypeCat.ofHom (Subtype.val : A → P)) ((objectsFiniteFunctor n).map h)
      ((posetCategorificationFiniteObjectsIso n hn P).inv ≫ (objectsFiniteFunctor n).map i) := by
  exact pushoutObjectCoordinateChange _ _ _ _ (pushout_finite_objects n hn _ _ _ _ H)
    (posetCategorificationFiniteObjectsIso n hn A) (posetCategorificationFiniteObjectsIso n hn P) _
    (by
      have he := posetCategorificationFiniteObjectsIso_natural n hn (P := (↑A : Type u)) (Q := P)
        (OrderEmbedding.subtype A).toOrderHom
      rw [show TypeCat.ofHom (OrderEmbedding.subtype A).toOrderHom =
        TypeCat.ofHom (Subtype.val : A → P) from rfl] at he
      exact he)

noncomputable def posetPushoutFiniteObjectsComplementIso (n : ℕ) (hn : 1 ≤ n)
    {P : Type u} [PartialOrder P] (A : Set P)
    {X Y : NCategory.{u} n} (a : (categorificationFinite n).obj (nerve A) ⟶ X)
    (h : X ⟶ Y) (i : (categorificationFinite n).obj (nerve P) ⟶ Y)
    (H : IsPushout a ((categorificationFinite n).map
      (nerveMap (OrderEmbedding.subtype A).toOrderHom.monotone.functor)) h i) :
    Y.val.Objects ≅ X.val.Objects ⊕ {p : P // p ∉ A} :=
  Attachments.pushoutComplementIso A
    ((posetCategorificationFiniteObjectsIso n hn A).inv ≫ (objectsFiniteFunctor n).map a)
    ((objectsFiniteFunctor n).map h)
    ((posetCategorificationFiniteObjectsIso n hn P).inv ≫ (objectsFiniteFunctor n).map i)
    (poset_pushout_finite_objects n hn A a h i H)

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.PosetTables

open CategoryTheory OmegaCategory DirectedComplex

variable {P : Type u} [PartialOrder P]

def fullOnVertices (S : Set P) : OmegaCategory.{u} :=
  ((complex P).nu.fullOn {a | tableObjectsEquiv (E := P) a ∈ S}).category

lemma segmentTableMap_objects_mem (S : Set P) (a : (complex S).nu.Objects) :
    tableObjectsEquiv (E := P) ((complexMap (OrderEmbedding.subtype S).toOrderHom).nu.objects a) ∈ S := by
  rw [Thomason.tableObjects_map]
  exact (tableObjectsEquiv (E := S) a).property

def segmentTableMap (S : Set P) : OmegaCategory.Functor (complex S).nu (fullOnVertices S) :=
  OmegaCategory.Functor.liftFullOn (C := (complex S).nu) (D := (complex P).nu)
    (complexMap (OrderEmbedding.subtype S).toOrderHom).nu
    {a : (complex P).nu.Objects | tableObjectsEquiv (E := P) a ∈ S} (by
      intro a
      exact segmentTableMap_objects_mem (P := P) S a)

lemma segmentTableMap_val (S : Set P) (x : Table (complex (↑S : Type u))) :
    ((segmentTableMap S).map x).val =
      (complexMap (OrderEmbedding.subtype S).toOrderHom).table x := rfl

lemma segmentTableMap_injective (S : Set P) : Function.Injective (segmentTableMap S).map := by
  intro x y h
  have he : (complexMap (OrderEmbedding.subtype S).toOrderHom).table x =
      (complexMap (OrderEmbedding.subtype S).toOrderHom).table y :=
    (segmentTableMap_val S x).symm.trans
      ((congrArg (fun z : (fullOnVertices S).Cell => z.val) h).trans (segmentTableMap_val S y))
  exact table_map_orderEmbedding_injective (E := (↑S : Type u)) (D := P)
    (OrderEmbedding.subtype S) he

lemma segmentTableMap_surjective (S : Set P) (hS : IsUpperSet S ∨ IsLowerSet S) :
    Function.Surjective (segmentTableMap S).map := by
  intro x
  change {x : Table (complex P) // x ∈
    ((complex P).nu.fullOn {a | tableObjectsEquiv (E := P) a ∈ S}).carrier} at x
  have hx : ∀ b, (x.val.row 0 b).val ∈ supportedOn S := by
    intro b
    cases b
    · rw [tableStart_row]
      apply bracket_mem_supportedOn
      intro a ha
      simp only [List.mem_singleton] at ha
      subst a
      exact x.property.1
    · rw [tableFinish_row]
      apply bracket_mem_supportedOn
      intro a ha
      simp only [List.mem_singleton] at ha
      subst a
      exact x.property.2
  obtain ⟨y, hy, _⟩ := table_segment_unique_lift_partial hS x.val hx
  exact ⟨y, Subtype.ext hy⟩

noncomputable def segmentTableIso (S : Set P) (hS : IsUpperSet S ∨ IsLowerSet S) :
    (complex S).nu ≅ fullOnVertices S :=
  isoOfBijective (segmentTableMap S)
    ⟨segmentTableMap_injective S, segmentTableMap_surjective S hS⟩

@[simp] lemma segmentTableIso_hom (S : Set P) (hS : IsUpperSet S ∨ IsLowerSet S) :
    (segmentTableIso S hS).hom = segmentTableMap S := rfl

lemma segmentTableIso_inclusion (S : Set P) (hS : IsUpperSet S ∨ IsLowerSet S) :
    (segmentTableIso S hS).hom ≫ ((complex P).nu.fullOn {a | tableObjectsEquiv (E := P) a ∈ S}).inclusion =
      (complexMap (OrderEmbedding.subtype S).toOrderHom).nu := rfl

end Thomason.NormalizedChains.PosetTables

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

variable {C : OmegaCategory.{u}}

def intervalFiberObjects (p : Functor C interval.{u}) (e : Fin 2) : Set C.Objects :=
  {a | p.objects a = intervalVertex e}

lemma interval_fiber_full_iff (p : Functor C interval.{u}) (e : Fin 2) (x : C.Cell) :
    p.map x = (intervalVertex e).val ↔
      C.sourceObject x ∈ intervalFiberObjects p e ∧ C.targetObject x ∈ intervalFiberObjects p e := by
  constructor
  · intro hx
    constructor
    · apply Subtype.ext
      change p.map (C.source 0 x) = _
      rw [p.map_source, hx]
      rfl
    · apply Subtype.ext
      change p.map (C.target 0 x) = _
      rw [p.map_target, hx]
      rfl
  · rintro ⟨hs, ht⟩
    apply ThinCell.ext
    · have he := congrArg ThinCell.left
        ((p.map_source 0 x).symm.trans (congrArg Subtype.val hs))
      exact he
    · have he := congrArg ThinCell.right
        ((p.map_target 0 x).symm.trans (congrArg Subtype.val ht))
      exact he

def intervalFiberFullIso (p : Functor C interval.{u}) (e : Fin 2) :
    (p.fiber (intervalVertex e)).category ≅ (C.fullOn (intervalFiberObjects p e)).category where
  hom := {
    map := fun x => ⟨x.val, (interval_fiber_full_iff p e x.val).mp x.property⟩
    map_source := fun _ _ => rfl
    map_target := fun _ _ => rfl
    map_comp := fun _ _ _ _ _ => rfl }
  inv := {
    map := fun x => ⟨x.val, (interval_fiber_full_iff p e x.val).mpr x.property⟩
    map_source := fun _ _ => rfl
    map_target := fun _ _ => rfl
    map_comp := fun _ _ _ _ _ => rfl }
  hom_inv_id := by apply Functor.ext; rfl
  inv_hom_id := by apply Functor.ext; rfl

lemma zero_fiber_isObjectSieve (p : Functor C interval.{u}) :
    C.IsObjectSieve (intervalFiberObjects p 0) := by
  intro x hx
  apply Subtype.ext
  change p.map (C.source 0 x) = _
  rw [p.map_source]
  have he : p.map (C.target 0 x) = (intervalVertex 0).val := congrArg Subtype.val hx
  rw [p.map_target] at he
  have hr : (p.map x).right.down = 0 := congrArg (fun a => a.right.down) he
  have hl : (p.map x).left.down = 0 := le_antisymm
    (by simpa only [hr] using (p.map x).related) (Fin.zero_le _)
  apply ThinCell.ext <;> apply ULift.ext <;> exact hl

lemma one_fiber_isObjectCosieve (p : Functor C interval.{u}) :
    C.IsObjectCosieve (intervalFiberObjects p 1) := by
  intro x hx
  apply Subtype.ext
  change p.map (C.target 0 x) = _
  rw [p.map_target]
  have he : p.map (C.source 0 x) = (intervalVertex 1).val := congrArg Subtype.val hx
  rw [p.map_source] at he
  have hl : (p.map x).left.down = 1 := congrArg (fun a => a.left.down) he
  have hr : (p.map x).right.down = 1 := le_antisymm
    (by exact Fin.le_last _) (by simpa only [hl] using (p.map x).related)
  apply ThinCell.ext <;> apply ULift.ext <;> exact hr

def maxLabel (p q : Functor C interval.{u}) : Functor C interval.{u} where
  map x := ⟨⟨max (p.map x).left.down (q.map x).left.down⟩,
    ⟨max (p.map x).right.down (q.map x).right.down⟩,
    max_le_max (p.map x).related (q.map x).related⟩
  map_source k x := by
    rw [p.map_source, q.map_source]
    cases k <;> rfl
  map_target k x := by
    rw [p.map_target, q.map_target]
    cases k <;> rfl
  map_comp k x y h h' := by
    rw [p.map_comp k x y h (p.map_composable h), q.map_comp k x y h (q.map_composable h)]
    cases k <;> rfl

def minLabel (p q : Functor C interval.{u}) : Functor C interval.{u} where
  map x := ⟨⟨min (p.map x).left.down (q.map x).left.down⟩,
    ⟨min (p.map x).right.down (q.map x).right.down⟩,
    min_le_min (p.map x).related (q.map x).related⟩
  map_source k x := by
    rw [p.map_source, q.map_source]
    cases k <;> rfl
  map_target k x := by
    rw [p.map_target, q.map_target]
    cases k <;> rfl
  map_comp k x y h h' := by
    rw [p.map_comp k x y h (p.map_composable h), q.map_comp k x y h (q.map_composable h)]
    cases k <;> rfl

lemma intervalCell_eq_vertex_iff (x : interval.{u}.Cell) (e : Fin 2) :
    x = (intervalVertex e).val ↔ x.left.down = e ∧ x.right.down = e := by
  constructor
  · intro h
    subst x
    exact ⟨rfl, rfl⟩
  · rintro ⟨hl, hr⟩
    apply ThinCell.ext
    · exact ULift.ext _ _ hl
    · exact ULift.ext _ _ hr

lemma maxLabel_zero_fiber (p q : Functor C interval.{u}) :
    ((maxLabel p q).fiber (intervalVertex 0)).carrier =
      (p.fiber (intervalVertex 0)).carrier ∩ (q.fiber (intervalVertex 0)).carrier := by
  ext x
  change (maxLabel p q).map x = (intervalVertex 0).val ↔
    p.map x = (intervalVertex 0).val ∧ q.map x = (intervalVertex 0).val
  simp only [intervalCell_eq_vertex_iff]
  rcases interval_cases (p.map x) with hp | hp | hp <;>
    rcases interval_cases (q.map x) with hq | hq | hq <;>
    simp [maxLabel, hp, hq, intervalVertex, intervalArrow]

lemma minLabel_one_fiber (p q : Functor C interval.{u}) :
    ((minLabel p q).fiber (intervalVertex 1)).carrier =
      (p.fiber (intervalVertex 1)).carrier ∩ (q.fiber (intervalVertex 1)).carrier := by
  ext x
  change (minLabel p q).map x = (intervalVertex 1).val ↔
    p.map x = (intervalVertex 1).val ∧ q.map x = (intervalVertex 1).val
  simp only [intervalCell_eq_vertex_iff]
  rcases interval_cases (p.map x) with hp | hp | hp <;>
    rcases interval_cases (q.map x) with hq | hq | hq <;>
    simp [minLabel, hp, hq, intervalVertex, intervalArrow]

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

noncomputable def truncationOverFunctor (n : ℕ) (hn : 1 ≤ n) :
    Over interval.{u} ⥤ Over (finiteInterval.{u} n hn) :=
  Over.post (truncationFunctor n) ⋙
    Over.map ((truncationAdjunction n).counit.app (finiteInterval n hn))

noncomputable def truncationOverAdjunction (n : ℕ) (hn : 1 ≤ n) :
    truncationOverFunctor.{u} n hn ⊣ Over.post (nCategoryInclusion n) :=
  Over.postAdjunctionRight (Y := finiteInterval n hn) (truncationAdjunction n)

def terminalConeFiniteInclusionIso (n : ℕ) (hn : 1 ≤ n) :
    terminalConeFiniteFunctor.{u} n hn ⋙ Over.post (nCategoryInclusion n) ≅
      nCategoryInclusion n ⋙ terminalConeFunctor :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

noncomputable def truncationZeroFiberIso (n : ℕ) (hn : 1 ≤ n) :
    truncationOverFunctor.{u} n hn ⋙ fiberFiniteFunctor n hn 0 ≅
      fiberFunctor (intervalVertex 0) ⋙ truncationFunctor n :=
  Adjunction.leftAdjointUniq
    (((truncationOverAdjunction n hn).comp (zeroFiberFiniteConeAdjunction n hn)).ofNatIsoRight
      (terminalConeFiniteInclusionIso n hn))
    (zeroFiberConeAdjunction.comp (truncationAdjunction n))

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.PosetTables

open CategoryTheory OmegaCategory DirectedComplex

variable {P : Type u} [PartialOrder P]

noncomputable def tableLabel (f : P →o Fin 2) : OmegaCategory.Functor (complex P).nu interval.{u} where
  map x := ⟨⟨f (tableStart x)⟩, ⟨f (tableFinish x)⟩, f.monotone (tableStart_le_finish x)⟩
  map_source k x := by
    apply ThinCell.ext
    · cases k <;> simp [interval, thin, ThinCell.source, ThinCell.vertex, tableStart]
    · cases k <;> simp [interval, thin, ThinCell.source, ThinCell.vertex, tableStart, tableFinish]
  map_target k x := by
    apply ThinCell.ext
    · cases k <;> simp [interval, thin, ThinCell.target, ThinCell.vertex, tableStart, tableFinish]
    · cases k <;> simp [interval, thin, ThinCell.target, ThinCell.vertex, tableFinish]
  map_comp k x y h h' := by
    apply ThinCell.ext
    · cases k <;> simp [interval, thin, ThinCell.comp, tableStart]
    · cases k with
      | zero => simp [interval, thin, ThinCell.comp, tableFinish]
      | succ k =>
        have he := congrArg (fun z => f (tableObjectsEquiv ((complex P).nu.targetObject z))) h
        simpa [interval, thin, ThinCell.comp, tableFinish] using congrArg (fun z : Fin 2 => (ULift.up z : ULift.{u} (Fin 2))) he.symm

def tableLabelFiberIso (f : P →o Fin 2) (e : Fin 2) :
    ((tableLabel f).fiber (intervalVertex e)).category ≅ fullOnVertices {a | f a = e} where
  hom := {
    map := fun x => ⟨x.val, (intervalCell_eq_vertex_iff ((tableLabel f).map x.val) e).mp x.property⟩
    map_source := fun _ _ => rfl
    map_target := fun _ _ => rfl
    map_comp := fun _ _ _ _ _ => rfl }
  inv := {
    map := fun x => ⟨x.val, (intervalCell_eq_vertex_iff ((tableLabel f).map x.val) e).mpr x.property⟩
    map_source := fun _ _ => rfl
    map_target := fun _ _ => rfl
    map_comp := fun _ _ _ _ _ => rfl }
  hom_inv_id := by apply OmegaCategory.Functor.ext; rfl
  inv_hom_id := by apply OmegaCategory.Functor.ext; rfl

lemma tableLabel_level_segment (f : P →o Fin 2) (e : Fin 2) :
    IsUpperSet {a | f a = e} ∨ IsLowerSet {a | f a = e} := by
  fin_cases e
  · right
    intro a b hab hb
    change f a = 0 at hb
    exact le_antisymm ((f.monotone hab).trans_eq hb) (Fin.zero_le _)
  · left
    intro a b hab ha
    change f a = 1 at ha
    exact le_antisymm (Fin.le_last _) (ha.symm.trans_le (f.monotone hab))

noncomputable def tableFiberSegmentIso (f : P →o Fin 2) (e : Fin 2) :
    (complex {a // f a = e}).nu ≅ ((tableLabel f).fiber (intervalVertex e)).category :=
  (segmentTableIso {a | f a = e} (tableLabel_level_segment f e)).trans
    (tableLabelFiberIso f e).symm

lemma tableFiberSegmentIso_inclusion (f : P →o Fin 2) (e : Fin 2) :
    (tableFiberSegmentIso f e).hom ≫ ((tableLabel f).fiber (intervalVertex e)).inclusion =
      (complexMap (OrderEmbedding.subtype {a | f a = e}).toOrderHom).nu := rfl

noncomputable def truncationTableZeroFiberIso (n : ℕ) (hn : 1 ≤ n) (f : P →o Fin 2) :
    (truncationFunctor n).obj (complex {a // f a = 0}).nu ≅
      (fiberFiniteFunctor n hn 0).obj ((truncationOverFunctor n hn).obj (Over.mk (tableLabel f))) :=
  ((truncationFunctor n).mapIso (tableFiberSegmentIso f 0)).trans
    ((truncationZeroFiberIso n hn).app (Over.mk (tableLabel f))).symm

end Thomason.NormalizedChains.PosetTables

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

def initialConeFunctor : OmegaCategory.{u} ⥤ Over interval.{u} :=
  opFunctor ⋙ terminalConeFunctor ⋙ reverseLabelFunctor

noncomputable def oneFiberConeAdjunction : fiberFunctor (intervalVertex 1) ⊣ initialConeFunctor.{u} :=
  (((reverseLabelEquivalence.toAdjunction).comp zeroFiberConeAdjunction).comp
    opEquivalence.toAdjunction).ofNatIsoLeft reversedZeroFiberNatIso

def initialConeFiniteFunctor (n : ℕ) (hn : 1 ≤ n) :
    NCategory.{u} n ⥤ Over (finiteInterval.{u} n hn) :=
  opFiniteFunctor n ⋙ terminalConeFiniteFunctor n hn ⋙ reverseLabelFiniteFunctor n hn

noncomputable def oneFiberFiniteConeAdjunction (n : ℕ) (hn : 1 ≤ n) :
    fiberFiniteFunctor.{u} n hn 1 ⊣ initialConeFiniteFunctor n hn :=
  ((((reverseLabelFiniteEquivalence n hn).toAdjunction).comp
    (zeroFiberFiniteConeAdjunction n hn)).comp
    (opFiniteEquivalence n).toAdjunction).ofNatIsoLeft (reversedZeroFiberFiniteNatIso n hn)

def initialConeFiniteInclusionIso (n : ℕ) (hn : 1 ≤ n) :
    initialConeFiniteFunctor.{u} n hn ⋙ Over.post (nCategoryInclusion n) ≅
      nCategoryInclusion n ⋙ initialConeFunctor :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

noncomputable def truncationOneFiberIso (n : ℕ) (hn : 1 ≤ n) :
    truncationOverFunctor.{u} n hn ⋙ fiberFiniteFunctor n hn 1 ≅
      fiberFunctor (intervalVertex 1) ⋙ truncationFunctor n :=
  Adjunction.leftAdjointUniq
    (((truncationOverAdjunction n hn).comp (oneFiberFiniteConeAdjunction n hn)).ofNatIsoRight
      (initialConeFiniteInclusionIso n hn))
    (oneFiberConeAdjunction.comp (truncationAdjunction n))

noncomputable def truncationFiberIso (n : ℕ) (hn : 1 ≤ n) (e : Fin 2) :
    truncationOverFunctor.{u} n hn ⋙ fiberFiniteFunctor n hn e ≅
      fiberFunctor (intervalVertex e) ⋙ truncationFunctor n := by
  by_cases he : e = 0
  · subst e
    exact truncationZeroFiberIso n hn
  · have he1 : e = 1 := by omega
    subst e
    exact truncationOneFiberIso n hn

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.PosetTables

open CategoryTheory OmegaCategory DirectedComplex

variable {P : Type u} [PartialOrder P]

noncomputable def truncationTableFiberIso (n : ℕ) (hn : 1 ≤ n) (f : P →o Fin 2) (e : Fin 2) :
    (truncationFunctor n).obj (complex {a // f a = e}).nu ≅
      (fiberFiniteFunctor n hn e).obj ((truncationOverFunctor n hn).obj (Over.mk (tableLabel f))) :=
  ((truncationFunctor n).mapIso (tableFiberSegmentIso f e)).trans
    ((truncationFiberIso n hn e).app (Over.mk (tableLabel f))).symm

end Thomason.NormalizedChains.PosetTables

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.PosetTables

open CategoryTheory OmegaCategory DirectedComplex

variable {P : Type u} [PartialOrder P] {Q : Type u} [PartialOrder Q]

@[simp] lemma tableStart_map (g : P →o Q) (x : Table (complex P)) :
    tableStart ((complexMap g).table x) = g (tableStart x) := by
  change tableObjectsEquiv ((complex Q).nu.sourceObject ((complexMap g).nu.map x)) = _
  have he : (complexMap g).nu.objects ((complex P).nu.sourceObject x) =
      (complex Q).nu.sourceObject ((complexMap g).nu.map x) := by
    apply Subtype.ext
    exact (complexMap g).nu.map_source 0 x
  rw [← he]
  exact Thomason.tableObjects_map g _

@[simp] lemma tableFinish_map (g : P →o Q) (x : Table (complex P)) :
    tableFinish ((complexMap g).table x) = g (tableFinish x) := by
  change tableObjectsEquiv ((complex Q).nu.targetObject ((complexMap g).nu.map x)) = _
  have he : (complexMap g).nu.objects ((complex P).nu.targetObject x) =
      (complex Q).nu.targetObject ((complexMap g).nu.map x) := by
    apply Subtype.ext
    exact (complexMap g).nu.map_target 0 x
  rw [← he]
  exact Thomason.tableObjects_map g _

lemma tableLabel_natural (g : P →o Q) (f : Q →o Fin 2) :
    OmegaCategory.Functor.comp (complexMap g).nu (tableLabel f) = tableLabel (f.comp g) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply ThinCell.ext
  · apply ULift.ext
    exact congrArg f (tableStart_map g x)
  · apply ULift.ext
    exact congrArg f (tableFinish_map g x)

noncomputable def lowerSegmentLabel (S : Set P) (hS : IsLowerSet S) : P →o Fin 2 := by
  classical
  exact {
    toFun := fun a => if a ∈ S then 0 else 1
    monotone' := by
      intro a b hab
      by_cases ha : a ∈ S
      · simp only [ite_eq_left ha]
        exact Fin.zero_le _
      · have hb : b ∉ S := fun hb => ha (hS hab hb)
        simp only [ite_eq_right ha, ite_eq_right hb, le_refl] }

@[simp] lemma lowerSegmentLabel_zero (S : Set P) (hS : IsLowerSet S) (a : P) :
    lowerSegmentLabel S hS a = 0 ↔ a ∈ S := by
  classical
  change (if a ∈ S then (0 : Fin 2) else 1) = 0 ↔ a ∈ S
  by_cases ha : a ∈ S <;> simp [ha]

noncomputable def upperSegmentLabel (S : Set P) (hS : IsUpperSet S) : P →o Fin 2 := by
  classical
  exact {
    toFun := fun a => if a ∈ S then 1 else 0
    monotone' := by
      intro a b hab
      by_cases ha : a ∈ S
      · have hb : b ∈ S := hS hab ha
        simp only [ite_eq_left ha, ite_eq_left hb, le_refl]
      · simp only [ite_eq_right ha]
        exact Fin.zero_le _ }

@[simp] lemma upperSegmentLabel_one (S : Set P) (hS : IsUpperSet S) (a : P) :
    upperSegmentLabel S hS a = 1 ↔ a ∈ S := by
  classical
  change (if a ∈ S then (1 : Fin 2) else 0) = 1 ↔ a ∈ S
  by_cases ha : a ∈ S <;> simp [ha]

end Thomason.NormalizedChains.PosetTables

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

noncomputable def truncationFiberComparison (n : ℕ) (hn : 1 ≤ n) (e : Fin 2)
    (p : Over interval.{u}) :
    (truncationFunctor n).obj ((fiberFunctor (intervalVertex e)).obj p) ⟶
      (fiberFiniteFunctor n hn e).obj ((truncationOverFunctor n hn).obj p) :=
  ((truncationAdjunction n).homEquiv _ _).symm
    ((fiberFunctor (intervalVertex e)).map ((truncationOverAdjunction n hn).unit.app p))

lemma truncationFiberComparison_unit (n : ℕ) (hn : 1 ≤ n) (e : Fin 2)
    (p : Over interval.{u}) :
    OmegaCategory.Functor.comp (truncationUnit n ((fiberFunctor (intervalVertex e)).obj p))
      (truncationFiberComparison n hn e p) =
        (fiberFunctor (intervalVertex e)).map ((truncationOverAdjunction n hn).unit.app p) :=
  ((truncationAdjunction n).homEquiv _ _).apply_symm_apply _

lemma truncationZeroFiberIso_inv_app (n : ℕ) (hn : 1 ≤ n) (p : Over interval.{u}) :
    (truncationZeroFiberIso n hn).inv.app p = truncationFiberComparison n hn 0 p := by
  apply ((truncationAdjunction n).homEquiv _ _).injective
  change OmegaCategory.Functor.comp (truncationUnit n _) ((truncationZeroFiberIso n hn).inv.app p) =
    OmegaCategory.Functor.comp (truncationUnit n _) (truncationFiberComparison n hn 0 p)
  rw [truncationFiberComparison_unit]
  let a := (((truncationOverAdjunction n hn).comp (zeroFiberFiniteConeAdjunction n hn)).ofNatIsoRight
    (terminalConeFiniteInclusionIso n hn))
  let b := zeroFiberConeAdjunction.comp (truncationAdjunction n)
  have hh := Adjunction.homEquiv_leftAdjointUniq_hom_app b a p
  change b.homEquiv p _ ((truncationZeroFiberIso n hn).inv.app p) = a.unit.app p at hh
  rw [Adjunction.comp_homEquiv] at hh
  simp only [zeroFiberConeAdjunction, truncationAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv, Equiv.trans_apply] at hh
  apply Functor.ext
  funext x
  have hcell := congrArg (fun H => H.left.map x.val) hh
  change (coneExtend p.hom
    (Functor.comp (truncationUnit n ((fiberFunctor (intervalVertex 0)).obj p))
      ((truncationZeroFiberIso n hn).inv.app p))).map x.val = _ at hcell
  rw [show (coneExtend p.hom
      (Functor.comp (truncationUnit n ((fiberFunctor (intervalVertex 0)).obj p))
      ((truncationZeroFiberIso n hn).inv.app p))).map x.val =
      ConeCell.old (((truncationZeroFiberIso n hn).inv.app p).map
        ((truncationUnit n ((fiberFunctor (intervalVertex 0)).obj p)).map x)) from
    coneExtendMap_zero p.hom _ x.val x.property] at hcell
  let q := (truncationOverFunctor n hn).obj p
  have hx : q.hom.map ((truncationUnit n p.left).map x.val) = (intervalVertex 0).val := by
    have h := congrArg (fun F => F.map x.val) (Over.w ((truncationOverAdjunction n hn).unit.app p))
    exact h.trans x.property
  change ConeCell.old _ = coneExtendMap q.hom (Functor.id _) ((truncationUnit n p.left).map x.val) at hcell
  rw [coneExtendMap_zero q.hom (Functor.id _) _ hx] at hcell
  exact ConeCell.old.inj hcell

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

def fiberFiniteInclusion (n : ℕ) (hn : 1 ≤ n) (e : Fin 2)
    (p : Over (finiteInterval.{u} n hn)) :
    (fiberFiniteFunctor n hn e).obj p ⟶ p.left :=
  (p.hom.fiber (intervalVertex e)).inclusion

lemma truncationFiberComparison_inclusion (n : ℕ) (hn : 1 ≤ n) (e : Fin 2)
    (p : Over interval.{u}) :
    truncationFiberComparison n hn e p ≫
      fiberFiniteInclusion n hn e ((truncationOverFunctor n hn).obj p) =
      (truncationFunctor n).map (p.hom.fiber (intervalVertex e)).inclusion := by
  apply truncation_functor_ext
  apply Functor.ext
  funext x
  have h := congrArg (fun F => F.map x) (truncationFiberComparison_unit n hn e p)
  exact congrArg Subtype.val h

lemma truncationZeroFiberIso_inv_inclusion (n : ℕ) (hn : 1 ≤ n)
    (p : Over interval.{u}) :
    (truncationZeroFiberIso n hn).inv.app p ≫
      fiberFiniteInclusion n hn 0 ((truncationOverFunctor n hn).obj p) =
      (truncationFunctor n).map (p.hom.fiber (intervalVertex 0)).inclusion := by
  rw [truncationZeroFiberIso_inv_app]
  exact truncationFiberComparison_inclusion n hn 0 p

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.PosetTables

open CategoryTheory OmegaCategory DirectedComplex

variable {P : Type u} [PartialOrder P]

lemma truncationTableZeroFiberIso_inclusion (n : ℕ) (hn : 1 ≤ n) (f : P →o Fin 2) :
    (truncationTableZeroFiberIso n hn f).hom ≫
      fiberFiniteInclusion n hn 0 ((truncationOverFunctor n hn).obj (Over.mk (tableLabel f))) =
      (truncationFunctor n).map
        (complexMap (OrderEmbedding.subtype {a | f a = 0}).toOrderHom).nu := by
  apply truncation_functor_ext
  apply OmegaCategory.Functor.ext
  funext x
  have h := congrArg (fun F => F.map ((tableFiberSegmentIso f 0).hom.map x))
    (truncationFiberComparison_unit n hn 0 (Over.mk (tableLabel f)))
  rw [← truncationZeroFiberIso_inv_app] at h
  exact congrArg Subtype.val h

end Thomason.NormalizedChains.PosetTables

end

end OAI
