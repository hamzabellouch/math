import OAI.CategoryTheory.Globular.Realization

namespace OAI

universe u v w

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularSet

def cutoffLow (X : GlobularSet.{u}) {q n : ℕ} (h : n ≤ q) :
    (X.cutoff q).Cell n ≃ X.Cell n := Equiv.cast (X.cutoffCell_low h)

def cutoffHigh (X : GlobularSet.{u}) {q n : ℕ} (h : q < n) :
    (X.cutoff q).Cell n ≃ X.Boundary (q+1) :=
  Equiv.cast (X.cutoffCell_high (Nat.not_le_of_gt h))

theorem cutoffFace_high (X : GlobularSet.{u}) {q n : ℕ} (h : q < n) (side) :
    HEq (X.cutoffFace q n side) (_root_.id : X.Boundary (q+1) → _) := by
  have hn : ¬ n+1 ≤ q := by omega
  have hne : n ≠ q := by omega
  simp only [cutoffFace, dite_eq_right hn, dite_eq_right hne]
  exact cast_heq _ _

private theorem coord_face {A B A' B' : Type u} (e : A ≃ A') (f : B ≃ B')
    (he : ∀ x, HEq (e x) x) (hf : ∀ x, HEq (f x) x)
    (g : A → B) (g' : A' → B') (hg : HEq g g') (x : A) :
    f (g x) = g' (e x) := by
  have ha : A = A' := (type_eq_of_heq (he x)).symm
  have hb : B = B' := (type_eq_of_heq (hf (g x))).symm
  cases ha; cases hb
  rw [eq_of_heq (hf (g x)), eq_of_heq hg, eq_of_heq (he x)]

theorem cutoffLow_face (X : GlobularSet.{u}) {q n : ℕ} (h : n+1 ≤ q)
    (side : Bool) (x : (X.cutoff q).Cell (n+1)) :
    X.cutoffLow (Nat.le_trans (Nat.le_succ n) h) (X.cutoffFace q n side x) =
      (if side then X.target n else X.source n) (X.cutoffLow h x) :=
  coord_face _ _ (fun _ => cast_heq _ _) (fun _ => cast_heq _ _)
    _ _ (X.cutoffFace_low h side) x

theorem cutoff_seam_face (X : GlobularSet.{u}) (q : ℕ) (side : Bool)
    (x : (X.cutoff q).Cell (q+1)) :
    X.cutoffLow (q := q) le_rfl (X.cutoffFace q q side x) =
      (if side then (X.cutoffHigh (Nat.lt_succ_self q) x).1.2
        else (X.cutoffHigh (Nat.lt_succ_self q) x).1.1) :=
  coord_face _ _ (fun _ => cast_heq _ _) (fun _ => cast_heq _ _)
    _ _ (X.cutoffFace_seam q side) x

theorem cutoff_high_face (X : GlobularSet.{u}) {q n : ℕ} (h : q < n)
    (side : Bool) (x : (X.cutoff q).Cell (n+1)) :
    X.cutoffHigh h (X.cutoffFace q n side x) =
      X.cutoffHigh (Nat.lt_trans h (Nat.lt_succ_self n)) x :=
  coord_face _ _ (fun _ => cast_heq _ _) (fun _ => cast_heq _ _)
    _ _ (X.cutoffFace_high h side) x

theorem cutoffLow_parallel (X : GlobularSet.{u}) {q n : ℕ} (h : n ≤ q)
    (x y : (X.cutoff q).Cell n) :
    (X.cutoff q).Parallel n x y ↔ X.Parallel n (X.cutoffLow h x) (X.cutoffLow h y) := by
  cases n with
  | zero => rfl
  | succ n =>
    change (_ = _ ∧ _ = _) ↔ (_ = _ ∧ _ = _)
    have hs z := X.cutoffLow_face h false z
    have ht z := X.cutoffLow_face h true z
    change ∀ z, X.cutoffLow _ ((X.cutoff q).source n z) = X.source n (X.cutoffLow h z) at hs
    change ∀ z, X.cutoffLow _ ((X.cutoff q).target n z) = X.target n (X.cutoffLow h z) at ht
    constructor
    · intro ⟨a, b⟩
      exact ⟨by rw [← hs, ← hs, a], by rw [← ht, ← ht, b]⟩
    · intro ⟨a, b⟩
      exact ⟨(X.cutoffLow _).injective (by rw [hs, hs, a]),
        (X.cutoffLow _).injective (by rw [ht, ht, b])⟩

theorem cutoff_boundary_seam_bijective (X : GlobularSet.{u}) (q : ℕ) :
    Function.Bijective ((X.cutoff q).boundary (q+1)) := by
  constructor
  · intro x y h
    apply (X.cutoffHigh (Nat.lt_succ_self q)).injective
    apply Subtype.ext
    apply Prod.ext
    · have hs := congrArg (fun b : (X.cutoff q).Boundary (q+1) =>
        X.cutoffLow (q := q) le_rfl b.1.1) h
      change X.cutoffLow _ (X.cutoffFace q q false x) =
        X.cutoffLow _ (X.cutoffFace q q false y) at hs
      rw [X.cutoff_seam_face q false x, X.cutoff_seam_face q false y] at hs
      exact hs
    · have ht := congrArg (fun b : (X.cutoff q).Boundary (q+1) =>
        X.cutoffLow (q := q) le_rfl b.1.2) h
      change X.cutoffLow _ (X.cutoffFace q q true x) =
        X.cutoffLow _ (X.cutoffFace q q true y) at ht
      rw [X.cutoff_seam_face q true x, X.cutoff_seam_face q true y] at ht
      exact ht
  · intro b
    let c : X.Boundary (q+1) :=
      ⟨(X.cutoffLow le_rfl b.1.1, X.cutoffLow le_rfl b.1.2),
        (X.cutoffLow_parallel le_rfl _ _).mp b.2⟩
    refine ⟨(X.cutoffHigh (Nat.lt_succ_self q)).symm c, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · apply (X.cutoffLow (q := q) le_rfl).injective
      change X.cutoffLow _ (X.cutoffFace q q false _) = _
      rw [X.cutoff_seam_face]
      change (X.cutoffHigh (Nat.lt_succ_self q)
        ((X.cutoffHigh (Nat.lt_succ_self q)).symm c)).1.1 = c.1.1
      exact congrArg (fun b : X.Boundary (q+1) => b.1.1)
        ((X.cutoffHigh (Nat.lt_succ_self q)).apply_symm_apply c)
    · apply (X.cutoffLow (q := q) le_rfl).injective
      change X.cutoffLow _ (X.cutoffFace q q true _) = _
      rw [X.cutoff_seam_face]
      change (X.cutoffHigh (Nat.lt_succ_self q)
        ((X.cutoffHigh (Nat.lt_succ_self q)).symm c)).1.2 = c.1.2
      exact congrArg (fun b : X.Boundary (q+1) => b.1.2)
        ((X.cutoffHigh (Nat.lt_succ_self q)).apply_symm_apply c)

theorem cutoff_boundary_bijective (X : GlobularSet.{u}) (q j : ℕ) (hj : q < j) :
    Function.Bijective ((X.cutoff q).boundary j) := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases h : j = q
    · subst j; exact X.cutoff_boundary_seam_bijective q
    have hq : q < j := by omega
    have hs (x : (X.cutoff q).Cell (j+1)) :
        X.cutoffHigh hq ((X.cutoff q).source j x) =
          X.cutoffHigh (Nat.lt_trans hq (Nat.lt_succ_self j)) x :=
      X.cutoff_high_face hq false x
    have ht (x : (X.cutoff q).Cell (j+1)) :
        X.cutoffHigh hq ((X.cutoff q).target j x) =
          X.cutoffHigh (Nat.lt_trans hq (Nat.lt_succ_self j)) x :=
      X.cutoff_high_face hq true x
    constructor
    · intro a b hab
      apply (X.cutoffHigh (Nat.lt_trans hq (Nat.lt_succ_self j))).injective
      rw [← hs, ← hs]
      exact congrArg (fun c : (X.cutoff q).Boundary (j+1) =>
        X.cutoffHigh hq c.1.1) hab
    · intro b
      have w : b.1.1 = b.1.2 := (ih hq).1
        (((X.cutoff q).parallel_iff_boundary_eq j _ _).mp b.2)
      let z := (X.cutoffHigh (Nat.lt_trans hq (Nat.lt_succ_self j))).symm
        (X.cutoffHigh hq b.1.1)
      refine ⟨z, Subtype.ext (Prod.ext ?_ ?_)⟩
      · apply (X.cutoffHigh hq).injective
        exact (hs z).trans (Equiv.apply_symm_apply _ _)
      · apply (X.cutoffHigh hq).injective
        exact (ht z).trans ((Equiv.apply_symm_apply _ _).trans (congrArg _ w))


theorem faceMap_parallel (X : GlobularSet.{u}) {q n : ℕ} (h : q < n) (x : X.Cell n) :
    X.Parallel q (X.faceMap h false x) (X.faceMap h true x) := by
  cases q with
  | zero => trivial
  | succ q =>
    constructor
    · simpa only [faceMap_succ, Bool.false_eq_true, ↓reduceIte] using (X.faceMap_comp (Nat.lt_succ_self q) h false false x).symm.trans
        (X.faceMap_comp (Nat.lt_succ_self q) h false true x)
    · simpa only [faceMap_succ, ↓reduceIte] using (X.faceMap_comp (Nat.lt_succ_self q) h true false x).symm.trans
        (X.faceMap_comp (Nat.lt_succ_self q) h true true x)

def cutoffUnitCell (X : GlobularSet.{u}) (q n : ℕ) (x : X.Cell n) : (X.cutoff q).Cell n :=
  if h : n ≤ q then (X.cutoffLow h).symm x
  else (X.cutoffHigh (Nat.lt_of_not_ge h)).symm
    ⟨(X.faceMap (Nat.lt_of_not_ge h) false x, X.faceMap (Nat.lt_of_not_ge h) true x),
      X.faceMap_parallel (Nat.lt_of_not_ge h) x⟩

@[simp]
theorem cutoffUnitCell_low (X : GlobularSet.{u}) {q n : ℕ} (h : n ≤ q) (x : X.Cell n) :
    X.cutoffLow h (X.cutoffUnitCell q n x) = x := by
  unfold cutoffUnitCell
  rw [dite_eq_left h]
  exact (X.cutoffLow h).apply_symm_apply x

@[simp]
theorem cutoffUnitCell_high (X : GlobularSet.{u}) {q n : ℕ} (h : q < n) (x : X.Cell n) :
    X.cutoffHigh h (X.cutoffUnitCell q n x) =
      ⟨(X.faceMap h false x, X.faceMap h true x), X.faceMap_parallel h x⟩ := by
  unfold cutoffUnitCell
  rw [dite_eq_right (Nat.not_le_of_gt h)]
  exact (X.cutoffHigh h).apply_symm_apply _

theorem cutoffUnitCell_face (X : GlobularSet.{u}) (q n : ℕ) (side : Bool)
    (x : X.Cell (n+1)) :
    X.cutoffUnitCell q n ((if side then X.target n else X.source n) x) =
      X.cutoffFace q n side (X.cutoffUnitCell q (n+1) x) := by
  by_cases h : n+1 ≤ q
  · apply (X.cutoffLow (Nat.le_trans (Nat.le_succ n) h)).injective
    rw [X.cutoffLow_face h side, X.cutoffUnitCell_low, X.cutoffUnitCell_low]
  · by_cases hn : n = q
    · subst n
      apply (X.cutoffLow (q := q) le_rfl).injective
      rw [X.cutoff_seam_face, X.cutoffUnitCell_low, X.cutoffUnitCell_high]
      cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, faceMap_succ]
    · have hq : q < n := by omega
      apply (X.cutoffHigh hq).injective
      rw [X.cutoff_high_face hq side, X.cutoffUnitCell_high, X.cutoffUnitCell_high]
      apply Subtype.ext
      apply Prod.ext
      · change X.faceMap hq false ((if side then X.target n else X.source n) x) =
          X.faceMap (Nat.lt_trans hq (Nat.lt_succ_self n)) false x
        rw [X.faceMap_source hq false]
        cases side
        · rfl
        · exact (X.faceMap_target hq false x).symm
      · change X.faceMap hq true ((if side then X.target n else X.source n) x) =
          X.faceMap (Nat.lt_trans hq (Nat.lt_succ_self n)) true x
        rw [X.faceMap_source hq true]
        cases side
        · rfl
        · exact (X.faceMap_target hq true x).symm

def cutoffUnit (X : GlobularSet.{u}) (q : ℕ) : Hom X (X.cutoff q) where
  app := X.cutoffUnitCell q
  source_app n x := X.cutoffUnitCell_face q n false x
  target_app n x := X.cutoffUnitCell_face q n true x

theorem cutoffUnit_bijective (X : GlobularSet.{u}) {q n : ℕ} (h : n ≤ q) :
    Function.Bijective ((X.cutoffUnit q).app n) := by
  have w : (X.cutoffUnit q).app n = (X.cutoffLow h).symm := by
    funext x
    apply (X.cutoffLow h).injective
    exact (X.cutoffUnitCell_low h x).trans ((X.cutoffLow h).apply_symm_apply x).symm
  rw [w]
  exact (X.cutoffLow h).symm.bijective

theorem Hom.evalFace_app {X Y : GlobularSet.{u}} (f : Hom X Y)
    {k j : ℕ} (a : Globe.Face k j) (x : X.Cell j) :
    f.app k (X.evalFace a x) = Y.evalFace a (f.app j x) := by
  cases a with
  | id => rfl
  | @face j h side =>
    change f.app k (X.faceMap h side x) = Y.faceMap h side (f.app j x)
    induction j, h using Nat.le_induction with
    | base =>
      simp only [faceMap_succ]
      cases side
      · exact f.source_app k x
      · exact f.target_app k x
    | succ j h ih =>
      rw [X.faceMap_source h side, Y.faceMap_source h side, ← f.source_app]
      exact ih (X.source j x)

def Hom.presheafMap {X Y : GlobularSet.{u}} (f : Hom X Y) : X.presheaf ⟶ Y.presheaf where
  app n := TypeCat.ofHom (f.app n.unop.dim)
  naturality _ _ a := ConcreteCategory.hom_ext _ _ (f.evalFace_app a.unop)

end GlobularSet

namespace GlobularPresheaf

noncomputable def tupleCellEquiv (X : GlobularPresheaf.{v}) (n : ℕ) :
    X.tuples.presheaf.obj (op (Shape.globe n)) ≃ X.obj (op (Globe.mk n)) where
  toFun f := f.app (op (Globe.mk n)) ⟨⟨𝟙 (Globe.mk n)⟩⟩
  invFun x :=
    { app k := TypeCat.ofHom (fun f => X.map f.down.down.op x)
      naturality k l f := by
        apply ConcreteCategory.hom_ext
        intro g
        change X.map (g.down.down.op ≫ f) x = X.map f (X.map g.down.down.op x)
        rw [X.map_comp]
        rfl }
  left_inv f := by
    apply NatTrans.ext
    funext k
    apply ConcreteCategory.hom_ext
    intro g
    let e : (Shape.liftedRealization.obj (Shape.globe n)).obj (op (Globe.mk n)) :=
      ⟨⟨𝟙 (Globe.mk n)⟩⟩
    have h := ConcreteCategory.congr_hom (f.naturality g.down.down.op) e
    change X.map g.down.down.op (f.app (op (Globe.mk n)) e) = f.app k g
    change f.app k ⟨⟨g.down.down ≫ 𝟙 (Globe.mk n)⟩⟩ =
      X.map g.down.down.op (f.app (op (Globe.mk n)) e) at h
    exact h.symm.trans (congrArg (fun t => f.app k t)
      (show (⟨⟨g.down.down ≫ 𝟙 (Globe.mk n)⟩⟩ :
        (Shape.liftedRealization.obj (Shape.globe n)).obj k) = g from
        by apply ULift.ext; apply ULift.ext; exact Category.comp_id _))
  right_inv x := by
    change X.map (𝟙 _) x = x
    rw [X.map_id]
    rfl

noncomputable def tuplesMap {X Y : GlobularPresheaf.{v}} (f : X ⟶ Y) :
    X.tuples.presheaf ⟶ Y.tuples.presheaf :=
  Functor.whiskerLeft Shape.liftedRealization.op (yoneda.map f)

@[simp]
theorem tupleCellEquiv_map {X Y : GlobularPresheaf.{v}} (f : X ⟶ Y) (n : ℕ)
    (x : X.tuples.presheaf.obj (op (Shape.globe n))) :
    Y.tupleCellEquiv n ((tuplesMap f).app (op (Shape.globe n)) x) =
      f.app (op (Globe.mk n)) (X.tupleCellEquiv n x) := rfl

theorem tupleCellEquiv_face (X : GlobularPresheaf.{v}) {m n : ℕ} (h : m < n)
    (side : Bool) (x : X.tuples.presheaf.obj (op (Shape.globe n))) :
    X.tupleCellEquiv m (X.tuples.presheaf.map (Shape.face h side).op x) =
      X.map (Globe.face h side).op (X.tupleCellEquiv n x) := by
  let e : (Shape.liftedRealization.obj (Shape.globe n)).obj (op (Globe.mk n)) :=
    ⟨⟨𝟙 (Globe.mk n)⟩⟩
  have w := ConcreteCategory.congr_hom (x.naturality (Globe.face h side).op) e
  change x.app (op (Globe.mk m)) ⟨⟨𝟙 (Globe.mk m) ≫ Globe.face h side⟩⟩ =
    X.map (Globe.face h side).op (x.app (op (Globe.mk n)) e)
  change x.app (op (Globe.mk m)) ⟨⟨Globe.face h side ≫ 𝟙 (Globe.mk n)⟩⟩ =
    X.map (Globe.face h side).op (x.app (op (Globe.mk n)) e) at w
  have hi := congrArg (fun a : Globe.mk m ⟶ Globe.mk n =>
    x.app (op (Globe.mk m)) ⟨⟨a⟩⟩) (Category.id_comp (Globe.face h side))
  have hc := congrArg (fun a : Globe.mk m ⟶ Globe.mk n =>
    x.app (op (Globe.mk m)) ⟨⟨a⟩⟩) (Category.comp_id (Globe.face h side))
  exact hi.trans (hc.symm.trans w)

noncomputable def tupleUnderlyingMap (X : GlobularPresheaf.{v}) :
    GlobularSet.Hom X.tuples.underlying X.underlying where
  app := fun n => X.tupleCellEquiv n
  source_app n x := X.tupleCellEquiv_face (Nat.lt_succ_self n) false x
  target_app n x := X.tupleCellEquiv_face (Nat.lt_succ_self n) true x

theorem tuplesMap_bijective_globe {X Y : GlobularPresheaf.{v}} (f : X ⟶ Y)
    (n : ℕ) (h : Function.Bijective (f.app (op (Globe.mk n)))) :
    Function.Bijective ((tuplesMap f).app (op (Shape.globe n))) := by
  have w : (tuplesMap f).app (op (Shape.globe n)) =
      (Y.tupleCellEquiv n).symm ∘ f.app (op (Globe.mk n)) ∘ X.tupleCellEquiv n := by
    funext x
    apply (Y.tupleCellEquiv n).injective
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using tupleCellEquiv_map f n x
  rw [w]
  exact (Y.tupleCellEquiv n).symm.bijective.comp (h.comp (X.tupleCellEquiv n).bijective)

end GlobularPresheaf

end Grothendieck

end OAI
