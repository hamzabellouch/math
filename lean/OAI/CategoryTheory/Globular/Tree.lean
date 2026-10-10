import OAI.CategoryTheory.Globular.LinearCells

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularTheory.Model

noncomputable def smallFreeDescCells {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f : ∀ k, S.underlying.Cell k → Y.obj.underlying.Cell k)
    (hs : ∀ k x, f k (S.underlying.source k x) = Y.obj.underlying.source k (f (k+1) x))
    (ht : ∀ k x, f k (S.underlying.target k x) = Y.obj.underlying.target k (f (k+1) x)) :
    (smallFree hC q).obj S ⟶ Y :=
  smallFreeDesc hC q
    { app := fun k x => f k x.down
      source_app := fun k x => hs k x.down
      target_app := fun k x => ht k x.down }

@[simp] theorem smallFreeDescCells_gen {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q}
    (f) (hs) (ht) (k : ℕ) (x : S.underlying.Cell k) :
    (underlyingMap (smallFreeDescCells hC q (Y := Y) f hs ht).hom).app k
      (smallFreeGen hC q S k x) = f k x := smallFreeDesc_gen hC q _ _ _

@[simp] theorem smallFreeCell_face {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S : GlobularPresheaf.{0}} {j k : ℕ} (h : j < k) (ε : Bool)
    (f : GlobularPresheaf.disk k ⟶ S) :
    ((smallFree hC q).obj S).obj.eval (C.base (Shape.face h ε)) (smallFreeCell hC q k f) =
      smallFreeCell hC q j (GlobularPresheaf.face h ε ≫ f) := by
  unfold smallFreeCell smallFreeGen
  have e := ((cutoffGlobularAdjunction hC q).unit.app (GlobularPresheaf.liftSmall.obj S)).naturality
    (Globe.face h ε).op
  have e' := ConcreteCategory.congr_hom e
    (show (GlobularPresheaf.liftSmall.{v}.obj S).obj (op (Globe.mk k)) from
      ULift.up (f.app (op (Globe.mk k)) (ULift.up (𝟙 (Globe.mk k)))))
  change ((cutoffGlobularAdjunction hC q).unit.app (GlobularPresheaf.liftSmall.obj S)).app
    (op (Globe.mk j)) (ULift.up (S.map (Globe.face h ε).op
      (f.app (op (Globe.mk k)) (ULift.up (𝟙 (Globe.mk k)))))) =
      ((smallFree hC q).obj S).obj.eval (C.base (Shape.face h ε)) _ at e'
  apply e'.symm.trans
  apply congrArg (((cutoffGlobularAdjunction hC q).unit.app (GlobularPresheaf.liftSmall.obj S)).app
    (op (Globe.mk j)))
  apply congrArg ULift.up
  exact (ConcreteCategory.congr_hom (f.naturality (Globe.face h ε).op)
    (show (GlobularPresheaf.disk k).obj (op (Globe.mk k)) from
      ULift.up (𝟙 (Globe.mk k)))).symm

noncomputable abbrev linearFree {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) :=
  (smallFree hC q).obj ((Shape.linearization n).obj S)

noncomputable def linLow {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (hk : k < n) (x : S.underlying.Cell k) :
    (linearFree hC q n S).obj.underlying.Cell k :=
  smallFreeCell hC q k (Shape.linearLow n S k hk x)

noncomputable def linEdge {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell n) :
    (linearFree hC q n S).obj.underlying.Cell (n+1) :=
  smallFreeCell hC q (n+1) (Shape.linearEdge n S x)

noncomputable def linMiddle {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell (n+1)) :
    (linearFree hC q n S).obj.underlying.Cell (n+1) :=
  smallFreeCell hC q (n+1) (Shape.realization.map (tripleMiddle n) ≫ Shape.linearTriple n S x)

@[simp] theorem linMiddle_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell (n+1)) :
    (linearFree hC q n S).obj.underlying.source n (linMiddle hC q n S x) =
      (linearFree hC q n S).obj.underlying.target n (linEdge hC q n S (S.underlying.source n x)) := by
  unfold linMiddle linEdge
  erw [smallFreeCell_source, smallFreeCell_target]
  apply congrArg (smallFreeCell hC q n)
  have e : GlobularPresheaf.face (Nat.lt_succ_self n) true ≫ Shape.realization.map (tripleFirst n) =
    GlobularPresheaf.face (Nat.lt_succ_self n) false ≫ Shape.realization.map (tripleMiddle n) :=
    triple_first_middle n
  calc
    _ = (GlobularPresheaf.face (Nat.lt_succ_self n) false ≫
      Shape.realization.map (tripleMiddle n)) ≫ Shape.linearTriple n S x :=
        (Category.assoc _ _ _).symm
    _ = (GlobularPresheaf.face (Nat.lt_succ_self n) true ≫
      Shape.realization.map (tripleFirst n)) ≫ Shape.linearTriple n S x :=
        congrArg (· ≫ Shape.linearTriple n S x) e.symm
    _ = _ := by
      erw [Category.assoc, Shape.linearTriple_face n S false x]
      rfl

@[simp] theorem linMiddle_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell (n+1)) :
    (linearFree hC q n S).obj.underlying.target n (linMiddle hC q n S x) =
      (linearFree hC q n S).obj.underlying.source n (linEdge hC q n S (S.underlying.target n x)) := by
  unfold linMiddle linEdge
  erw [smallFreeCell_target, smallFreeCell_source]
  apply congrArg (smallFreeCell hC q n)
  have e : GlobularPresheaf.face (Nat.lt_succ_self n) true ≫ Shape.realization.map (tripleMiddle n) =
    GlobularPresheaf.face (Nat.lt_succ_self n) false ≫ Shape.realization.map (tripleLast n) :=
    triple_middle_last n
  calc
    _ = (GlobularPresheaf.face (Nat.lt_succ_self n) true ≫
      Shape.realization.map (tripleMiddle n)) ≫ Shape.linearTriple n S x :=
        (Category.assoc _ _ _).symm
    _ = (GlobularPresheaf.face (Nat.lt_succ_self n) false ≫
      Shape.realization.map (tripleLast n)) ≫ Shape.linearTriple n S x :=
        congrArg (· ≫ Shape.linearTriple n S x) e
    _ = _ := by
      erw [Category.assoc, Shape.linearTriple_face n S true x]
      rfl

@[simp] theorem linLow_face {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) {j k : ℕ} (h : j < k) (hk : k < n)
    (ε : Bool) (x : S.underlying.Cell k) :
    (linearFree hC q n S).obj.eval (C.base (Shape.face h ε)) (linLow hC q n S k hk x) =
      linLow hC q n S j (h.trans hk) (S.map (Globe.face h ε).op x) := by
  unfold linLow
  erw [smallFreeCell_face, Shape.linearLow_face]

@[simp] theorem linEdge_face {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) {j : ℕ} (h : j < n)
    (ε : Bool) (x : S.underlying.Cell n) :
    (linearFree hC q n S).obj.eval (C.base (Shape.face (by omega : j < n+1) ε))
      (linEdge hC q n S x) = linLow hC q n S j h (S.map (Globe.face h ε).op x) := by
  unfold linEdge linLow
  erw [smallFreeCell_face, Shape.linearEdge_face]

noncomputable def linOriginal {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0})
    (hS : ∀ k, n+1 < k → IsEmpty (S.underlying.Cell k))
    (k : ℕ) (x : S.underlying.Cell k) : (linearFree hC q n S).obj.underlying.Cell k := by
  by_cases h : k < n
  · exact linLow hC q n S k h x
  · by_cases e : k = n
    · subst k
      exact (linearFree hC q n S).obj.underlying.source n (linEdge hC q n S x)
    · have ek : k = n+1 := by
        by_contra hn
        exact (hS k (by omega)).false x
      subst k
      exact (linearFree hC q n S).obj.compCell hC n
        (linEdge hC q n S (S.underlying.source n x)) (linMiddle hC q n S x)
        (linMiddle_source hC q n S x).symm

@[simp] theorem linOriginal_low {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (k : ℕ) (hk : k < n)
    (x : S.underlying.Cell k) : linOriginal hC q n S hS k x = linLow hC q n S k hk x := by
  unfold linOriginal
  rw [dite_eq_left hk]

@[simp] theorem linOriginal_center {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (x : S.underlying.Cell n) :
    linOriginal hC q n S hS n x =
      (linearFree hC q n S).obj.underlying.source n (linEdge hC q n S x) := by
  unfold linOriginal
  rw [dite_eq_right (lt_irrefl n), dite_eq_left rfl]

@[simp] theorem linOriginal_high {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (x : S.underlying.Cell (n+1)) :
    linOriginal hC q n S hS (n+1) x =
      (linearFree hC q n S).obj.compCell hC n
        (linEdge hC q n S (S.underlying.source n x)) (linMiddle hC q n S x)
        (linMiddle_source hC q n S x).symm := by
  unfold linOriginal
  rw [dite_eq_right (by omega), dite_eq_right (by omega)]

theorem linOriginal_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (k : ℕ) (x : S.underlying.Cell (k+1)) :
    linOriginal hC q n S hS k (S.underlying.source k x) =
      (linearFree hC q n S).obj.underlying.source k (linOriginal hC q n S hS (k+1) x) := by
  have hk : k ≤ n := by
    by_contra h
    exact (hS (k+1) (by omega)).false x
  by_cases he : k = n
  · subst k
    erw [linOriginal_center, linOriginal_high, compCell_source]
  · have hkn : k < n := by omega
    erw [linOriginal_low _ _ _ _ _ _ hkn]
    by_cases e : k+1 = n
    · subst n
      erw [linOriginal_center]
      change _ = (linearFree hC q (k+1) S).obj.eval (C.base (Shape.source k))
        ((linearFree hC q (k+1) S).obj.eval (C.base (Shape.source (k+1))) _)
      erw [← eval_comp, ← C.base_comp]
      erw [← Shape.face_two_source]
      exact (linEdge_face hC q (k+1) S (Nat.lt_succ_self k) false x).symm
    · have h' : k+1 < n := by omega
      erw [linOriginal_low _ _ _ _ _ _ h']
      exact (linLow_face hC q n S (Nat.lt_succ_self k) h' false x).symm

theorem linOriginal_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (k : ℕ) (x : S.underlying.Cell (k+1)) :
    linOriginal hC q n S hS k (S.underlying.target k x) =
      (linearFree hC q n S).obj.underlying.target k (linOriginal hC q n S hS (k+1) x) := by
  have hk : k ≤ n := by
    by_contra h
    exact (hS (k+1) (by omega)).false x
  by_cases he : k = n
  · subst k
    erw [linOriginal_center, linOriginal_high, compCell_target, linMiddle_target]
  · have hkn : k < n := by omega
    erw [linOriginal_low _ _ _ _ _ _ hkn]
    by_cases e : k+1 = n
    · subst n
      erw [linOriginal_center]
      change _ = (linearFree hC q (k+1) S).obj.eval (C.base (Shape.target k))
        ((linearFree hC q (k+1) S).obj.eval (C.base (Shape.source (k+1))) _)
      erw [← eval_comp, ← C.base_comp]
      erw [← Shape.face_two_source]
      exact (linEdge_face hC q (k+1) S (Nat.lt_succ_self k) true x).symm
    · have h' : k+1 < n := by omega
      erw [linOriginal_low _ _ _ _ _ _ h']
      exact (linLow_face hC q n S (Nat.lt_succ_self k) h' true x).symm

noncomputable def whiskerToLinearCell {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0})
    (hS : ∀ k, n+1 < k → IsEmpty (S.underlying.Cell k))
    (k : ℕ) (x : (S.underlying.whisker n false).Cell k) :
    (linearFree hC q n S).obj.underlying.Cell k :=
  match x with
  | .base k x => linOriginal hC q n S hS k x
  | .tip x => (linearFree hC q n S).obj.underlying.target n (linEdge hC q n S x)
  | .edge x => linEdge hC q n S x

theorem whiskerToLinearCell_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (k : ℕ)
    (x : (S.underlying.whisker n false).Cell (k+1)) :
    whiskerToLinearCell hC q n S hS k ((S.underlying.whisker n false).source k x) =
      (linearFree hC q n S).obj.underlying.source k (whiskerToLinearCell hC q n S hS (k+1) x) := by
  cases x with
  | base k x => exact linOriginal_source hC q n S hS k x
  | tip x =>
    change linOriginal hC q (k+1) S hS k (S.underlying.source k x) = _
    rw [linOriginal_source, linOriginal_center]
    exact (linearFree hC q (k+1) S).obj.underlying.source_source k _
  | edge x => exact linOriginal_center hC q n S hS x

theorem whiskerToLinearCell_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (k : ℕ)
    (x : (S.underlying.whisker n false).Cell (k+1)) :
    whiskerToLinearCell hC q n S hS k ((S.underlying.whisker n false).target k x) =
      (linearFree hC q n S).obj.underlying.target k (whiskerToLinearCell hC q n S hS (k+1) x) := by
  cases x with
  | base k x => exact linOriginal_target hC q n S hS k x
  | tip x =>
    change linOriginal hC q (k+1) S hS k (S.underlying.target k x) = _
    rw [linOriginal_target, linOriginal_center]
    exact (linearFree hC q (k+1) S).obj.underlying.target_source k _
  | edge x => rfl

noncomputable abbrev whiskerFree {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) :=
  (smallFree hC q).obj ((GlobularPresheaf.whiskering n false).obj S)

noncomputable def whiskerToLinear {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0})
    (hS : ∀ k, n+1 < k → IsEmpty (S.underlying.Cell k)) : whiskerFree hC q n S ⟶ linearFree hC q n S :=
  smallFreeDescCells hC q (whiskerToLinearCell hC q n S hS)
    (fun k x => by
      have e := (S.underlying.whisker n false).presheafUnderlyingMap.source_app k x
      change ((GlobularPresheaf.whiskering n false).obj S).underlying.source k x =
        (S.underlying.whisker n false).source k x at e
      exact (congrArg (whiskerToLinearCell hC q n S hS k) e).trans
        (whiskerToLinearCell_source hC q n S hS k x))
    (fun k x => by
      have e := (S.underlying.whisker n false).presheafUnderlyingMap.target_app k x
      change ((GlobularPresheaf.whiskering n false).obj S).underlying.target k x =
        (S.underlying.whisker n false).target k x at e
      exact (congrArg (whiskerToLinearCell hC q n S hS k) e).trans
        (whiskerToLinearCell_target hC q n S hS k x))

noncomputable def wBase {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell k) :
    (whiskerFree hC q n S).obj.underlying.Cell k :=
  smallFreeGen hC q ((GlobularPresheaf.whiskering n false).obj S) k (.base k x)

noncomputable def wEdge {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell n) :
    (whiskerFree hC q n S).obj.underlying.Cell (n+1) :=
  smallFreeGen hC q ((GlobularPresheaf.whiskering n false).obj S) (n+1) (.edge x)

@[simp] theorem wBase_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell (k+1)) :
    (whiskerFree hC q n S).obj.underlying.source k (wBase hC q n S (k+1) x) =
      wBase hC q n S k (S.underlying.source k x) := by
  unfold wBase
  erw [smallFreeGen_source]
  congr 1
  exact (S.underlying.whisker n false).presheafUnderlyingMap.source_app _ _

@[simp] theorem wBase_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (x : S.underlying.Cell (k+1)) :
    (whiskerFree hC q n S).obj.underlying.target k (wBase hC q n S (k+1) x) =
      wBase hC q n S k (S.underlying.target k x) := by
  unfold wBase
  erw [smallFreeGen_target]
  congr 1
  exact (S.underlying.whisker n false).presheafUnderlyingMap.target_app _ _

@[simp] theorem wEdge_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell n) :
    (whiskerFree hC q n S).obj.underlying.source n (wEdge hC q n S x) = wBase hC q n S n x := by
  unfold wEdge wBase
  erw [smallFreeGen_source]
  congr 1
  exact (S.underlying.whisker n false).presheafUnderlyingMap.source_app _ _

noncomputable def wMiddle {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell (n+1)) :
    (whiskerFree hC q n S).obj.underlying.Cell (n+1) :=
  (whiskerFree hC q n S).obj.compCell hC n
    ((whiskerFree hC q n S).obj.inverseCell hC n (wEdge hC q n S (S.underlying.source n x)))
    (wBase hC q n S (n+1) x) (by rw [inverseCell_target, wEdge_source, wBase_source])

@[simp] theorem wMiddle_source {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell (n+1)) :
    (whiskerFree hC q n S).obj.underlying.source n (wMiddle hC q n S x) =
      (whiskerFree hC q n S).obj.underlying.target n (wEdge hC q n S (S.underlying.source n x)) := by
  unfold wMiddle
  rw [compCell_source, inverseCell_source]

@[simp] theorem wMiddle_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell (n+1)) :
    (whiskerFree hC q n S).obj.underlying.target n (wMiddle hC q n S x) =
      (whiskerFree hC q n S).obj.underlying.source n (wEdge hC q n S (S.underlying.target n x)) := by
  unfold wMiddle
  rw [compCell_target, wBase_target, wEdge_source]

noncomputable def wTriple {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell (n+1)) :
    (whiskerFree hC q n S).obj.presheaf.obj (op (⟨tripleShape n⟩ : C.Obj)) :=
  (whiskerFree hC q n S).obj.tripleTuple n
    (wEdge hC q n S (S.underlying.source n x)) (wMiddle hC q n S x)
    (wEdge hC q n S (S.underlying.target n x))
    (wMiddle_source hC q n S x).symm (wMiddle_target hC q n S x)

noncomputable def linReverseBlock {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (hk : k ≤ n+1)
    (x : S.underlying.Cell k) :
    (smallFree hC q).obj ((Shape.linearGlobularDiagram n).obj k hk) ⟶ whiskerFree hC q n S := by
  by_cases h : k < n
  · exact (smallFree hC q).map (Shape.realization.map (eqToHom (Shape.linearBlock_low n k h))) ≫
      smallDiskDesc hC q k (wBase hC q n S k x)
  · by_cases e : k = n
    · subst k
      exact (smallFree hC q).map (Shape.realization.map (eqToHom (Shape.linearBlock_center n n rfl))) ≫
        smallDiskDesc hC q (n+1) (wEdge hC q n S x)
    · have ek : k = n+1 := by omega
      subst k
      exact (smallFree hC q).map (Shape.realization.map (eqToHom (Shape.linearBlock_high n (n+1) (by omega)))) ≫
        smallShapeDesc hC q (tripleShape n) (wTriple hC q n S x)

@[simp] theorem linReverseBlock_low {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (hk : k ≤ n+1) (h : k < n)
    (x : S.underlying.Cell k) : linReverseBlock hC q n S k hk x =
    (smallFree hC q).map (Shape.realization.map (eqToHom (Shape.linearBlock_low n k h))) ≫
      smallDiskDesc hC q k (wBase hC q n S k x) := by
  unfold linReverseBlock
  rw [dite_eq_left h]
  rfl

@[simp] theorem linReverseBlock_center {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hk : n ≤ n+1) (x : S.underlying.Cell n) :
    linReverseBlock hC q n S n hk x =
    (smallFree hC q).map (Shape.realization.map (eqToHom (Shape.linearBlock_center n n rfl))) ≫
      smallDiskDesc hC q (n+1) (wEdge hC q n S x) := by
  unfold linReverseBlock
  rw [dite_eq_right (lt_irrefl n), dite_eq_left rfl]
  rfl

@[simp] theorem linReverseBlock_high {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hk : n+1 ≤ n+1) (x : S.underlying.Cell (n+1)) :
    linReverseBlock hC q n S (n+1) hk x =
    (smallFree hC q).map (Shape.realization.map (eqToHom (Shape.linearBlock_high n (n+1) (by omega)))) ≫
      smallShapeDesc hC q (tripleShape n) (wTriple hC q n S x) := by
  unfold linReverseBlock
  rw [dite_eq_right (by omega), dite_eq_right (by omega)]
  rfl

theorem transportedShapeDesc {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {A B D E : Shape} (e : A = B) (f : B ⟶ D) (e' : E = D)
    {Y : CutoffModels C q} (t : Y.obj.presheaf.obj (op (⟨D⟩ : C.Obj))) :
    (smallFree hC q).map (Shape.realization.map (eqToHom e ≫ f ≫ eqToHom e'.symm)) ≫
      (smallFree hC q).map (Shape.realization.map (eqToHom e')) ≫ smallShapeDesc hC q D t =
    (smallFree hC q).map (Shape.realization.map (eqToHom e)) ≫
      smallShapeDesc hC q B (Y.obj.eval (C.base f) t) := by
  subst B
  subst E
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  erw [Shape.realization.map_id, (smallFree hC q).map_id, Category.id_comp,
    smallShapeDesc_naturality]
  erw [Shape.realization.map_id, (smallFree hC q).map_id, Category.id_comp]

theorem linReverseBlock_adjacent {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (k : ℕ) (hk : k+1 ≤ n+1)
    (ε : Bool) (x : S.underlying.Cell (k+1)) :
    (smallFree hC q).map ((Shape.linearGlobularDiagram n).face (Nat.lt_succ_self k) hk ε) ≫
      linReverseBlock hC q n S (k+1) hk x =
      linReverseBlock hC q n S k (by omega) (S.map (Globe.face (Nat.lt_succ_self k) ε).op x) := by
  by_cases e : k = n
  · subst k
    erw [Shape.linear_face_top, linReverseBlock_center, linReverseBlock_high]
    erw [transportedShapeDesc]
    unfold smallDiskDesc
    congr 2
    cases ε <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact tripleTuple_first _ _ _ _ _ _ _
    · exact tripleTuple_last _ _ _ _ _ _ _
  · have h : k < n := by omega
    by_cases e' : k+1 = n
    · subst n
      erw [Shape.linear_face_center, linReverseBlock_low _ _ _ _ _ _ h, linReverseBlock_center]
      unfold smallDiskDesc
      erw [transportedShapeDesc]
      congr 2
      erw [Shape.face_two_source, C.base_comp, eval_comp]
      cases ε
      · exact (congrArg ((whiskerFree hC q (k+1) S).obj.underlying.source k)
          (wEdge_source hC q (k+1) S x)).trans (wBase_source hC q (k+1) S k x)
      · exact (congrArg ((whiskerFree hC q (k+1) S).obj.underlying.target k)
          (wEdge_source hC q (k+1) S x)).trans (wBase_target hC q (k+1) S k x)
    · have h' : k+1 < n := by omega
      erw [Shape.linear_face_low _ _ _ _ h', linReverseBlock_low _ _ _ _ _ _ h',
        linReverseBlock_low _ _ _ _ _ _ h]
      unfold smallDiskDesc
      erw [transportedShapeDesc]
      congr 2
      cases ε
      · exact wBase_source hC q n S k x
      · exact wBase_target hC q n S k x

noncomputable def linearToWhisker {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0})
    (hS : ∀ k, n+1 < k → IsEmpty (S.underlying.Cell k)) : linearFree hC q n S ⟶ whiskerFree hC q n S :=
  GlobularPresheaf.finiteRealizationDesc (smallFree hC q) (Shape.linearGlobularDiagram n)
    S hS (whiskerFree hC q n S) (linReverseBlock hC q n S)
    ((Shape.linearGlobularDiagram n).face_natural (smallFree hC q) S (whiskerFree hC q n S)
      (linReverseBlock hC q n S) (fun k hk ε x => by
        rw [← FiniteCoGlobularObject.face_succ]
        exact linReverseBlock_adjacent hC q n S k hk ε x))

theorem cancelShapeTransport {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {A B : Shape} (e : A = B) {Y : CutoffModels C q}
    (f : (smallFree hC q).obj B.realize ⟶ Y) :
    (smallFree hC q).map (Shape.realization.map (eqToHom e.symm)) ≫
      (smallFree hC q).map (Shape.realization.map (eqToHom e)) ≫ f = f := by
  subst B
  erw [Shape.realization.map_id, (smallFree hC q).map_id, Category.id_comp, Category.id_comp]

@[reassoc] theorem linearToWhisker_lowHom {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (k : ℕ) (hk : k < n)
    (x : S.underlying.Cell k) :
    (smallFree hC q).map (Shape.linearLow n S k hk x) ≫ linearToWhisker hC q n S hS =
      smallDiskDesc hC q k (wBase hC q n S k x) := by
  unfold Shape.linearLow linearToWhisker
  erw [(smallFree hC q).map_comp, Category.assoc, GlobularPresheaf.finiteRealizationDesc_cell]
  erw [linReverseBlock_low _ _ _ _ _ _ hk, cancelShapeTransport]

@[reassoc] theorem linearToWhisker_edgeHom {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (x : S.underlying.Cell n) :
    (smallFree hC q).map (Shape.linearEdge n S x) ≫ linearToWhisker hC q n S hS =
      smallDiskDesc hC q (n+1) (wEdge hC q n S x) := by
  unfold Shape.linearEdge linearToWhisker
  erw [(smallFree hC q).map_comp, Category.assoc, GlobularPresheaf.finiteRealizationDesc_cell]
  erw [linReverseBlock_center, cancelShapeTransport]

@[reassoc] theorem linearToWhisker_tripleHom {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (x : S.underlying.Cell (n+1)) :
    (smallFree hC q).map (Shape.linearTriple n S x) ≫ linearToWhisker hC q n S hS =
      smallShapeDesc hC q (tripleShape n) (wTriple hC q n S x) := by
  unfold Shape.linearTriple linearToWhisker
  erw [(smallFree hC q).map_comp, Category.assoc, GlobularPresheaf.finiteRealizationDesc_cell]
  erw [linReverseBlock_high, cancelShapeTransport]

theorem smallFreeCell_image {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q : ℕ) {S : GlobularPresheaf.{0}} {Y : CutoffModels C q} (k : ℕ)
    (a : GlobularPresheaf.disk k ⟶ S) (f : (smallFree hC q).obj S ⟶ Y)
    (x : Y.obj.underlying.Cell k) (h : (smallFree hC q).map a ≫ f = smallDiskDesc hC q k x) :
    (underlyingMap f.hom).app k (smallFreeCell hC q k a) = x := by
  have e := congrFun (congrArg (fun z => (underlyingMap z.hom).app k) h)
    (smallFreeGen hC q (GlobularPresheaf.disk k) k (ULift.up (𝟙 (Globe.mk k))))
  change (underlyingMap f.hom).app k
    ((underlyingMap ((smallFree hC q).map a).hom).app k _) = _ at e
  have hm : (underlyingMap ((smallFree hC q).map a).hom).app k
      (smallFreeGen hC q (GlobularPresheaf.disk k) k (ULift.up (𝟙 (Globe.mk k)))) =
      smallFreeCell hC q k a := smallFreeGen_map hC q a k _
  exact ((congrArg (underlyingMap f.hom |>.app k) hm).symm.trans e).trans
    (smallDiskDesc_gen hC q k x)

@[simp] theorem linearToWhisker_low {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (k : ℕ) (hk : k < n) (x : S.underlying.Cell k) :
    (underlyingMap (linearToWhisker hC q n S hS).hom).app k (linLow hC q n S k hk x) =
      wBase hC q n S k x :=
  smallFreeCell_image hC q k _ _ _ (linearToWhisker_lowHom hC q n S hS k hk x)

@[simp] theorem linearToWhisker_edge {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (x : S.underlying.Cell n) :
    (underlyingMap (linearToWhisker hC q n S hS).hom).app (n+1) (linEdge hC q n S x) =
      wEdge hC q n S x :=
  smallFreeCell_image hC q (n+1) _ _ _ (linearToWhisker_edgeHom hC q n S hS x)

@[simp] theorem linearToWhisker_middle {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (x : S.underlying.Cell (n+1)) :
    (underlyingMap (linearToWhisker hC q n S hS).hom).app (n+1) (linMiddle hC q n S x) =
      wMiddle hC q n S x := by
  let a : GlobularPresheaf.disk (n+1) ⟶ (tripleShape n).realize :=
    Shape.realization.map (tripleMiddle n)
  have he : (smallFree hC q).map a ≫ smallShapeDesc hC q (tripleShape n) (wTriple hC q n S x) =
      smallDiskDesc hC q (n+1) (wMiddle hC q n S x) := by
    have e := smallShapeDesc_naturality hC q (tripleMiddle n) (wTriple hC q n S x)
    have ht : (whiskerFree hC q n S).obj.eval (C.base (tripleMiddle n)) (wTriple hC q n S x) =
        wMiddle hC q n S x := tripleTuple_middle _ _ _ _ _ _ _
    exact e.trans (congrArg (smallShapeDesc hC q (Shape.globe (n+1))) ht)
  apply smallFreeCell_image hC q (n+1) (a ≫ Shape.linearTriple n S x)
  calc
    _ = (smallFree hC q).map a ≫
        ((smallFree hC q).map (Shape.linearTriple n S x) ≫ linearToWhisker hC q n S hS) := by
      rw [(smallFree hC q).map_comp, Category.assoc]
    _ = (smallFree hC q).map a ≫ smallShapeDesc hC q (tripleShape n) (wTriple hC q n S x) :=
      congrArg (_ ≫ ·) (linearToWhisker_tripleHom hC q n S hS x)
    _ = _ := he

theorem compCell_cancel_left {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (a b : X.underlying.Cell (n+1))
    (h : X.underlying.source n a = X.underlying.source n b) :
    X.underlying.Joined (n+1)
      (X.compCell hC n a
        (X.compCell hC n (X.inverseCell hC n a) b (by rw [inverseCell_target, h]))
        (by rw [compCell_source, inverseCell_source])) b := by
  have hi := X.compCell_assoc hC n a (X.inverseCell hC n a) b
    (X.inverseCell_source hC n a).symm (by rw [inverseCell_target, h])
  apply X.joined_trans hC (X.joined_symm hC hi)
  apply X.joined_trans hC (X.compCell_congr_left hC n
    (X.compCell hC n a (X.inverseCell hC n a) (X.inverseCell_source hC n a).symm)
    (X.unitCell hC n (X.underlying.source n a)) b
    (by rw [compCell_target, inverseCell_target, h])
    (by rw [unitCell_target, h]) (X.compCell_inverse_right hC n a))
  simpa only [h] using X.compCell_left_unit hC n b

@[simp] theorem whiskerToLinear_gen {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (k : ℕ)
    (x : ((GlobularPresheaf.whiskering n false).obj S).underlying.Cell k) :
    (underlyingMap (whiskerToLinear hC q n S hS).hom).app k
      (smallFreeGen hC q ((GlobularPresheaf.whiskering n false).obj S) k x) =
    whiskerToLinearCell hC q n S hS k x := smallFreeDescCells_gen hC q _ _ _ k x

@[simp] theorem wEdge_target {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (x : S.underlying.Cell n) :
    (whiskerFree hC q n S).obj.underlying.target n (wEdge hC q n S x) =
      smallFreeGen hC q ((GlobularPresheaf.whiskering n false).obj S) n (.tip x) := by
  unfold wEdge
  erw [smallFreeGen_target]
  congr 1
  exact (S.underlying.whisker n false).presheafUnderlyingMap.target_app _ _

theorem whiskerLinear_low {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS) (k : ℕ) (hk : k ≤ n)
    (x : ((GlobularPresheaf.whiskering n false).obj S).underlying.Cell k) :
    (underlyingMap (whiskerToLinear hC q n S hS ≫ linearToWhisker hC q n S hS).hom).app k
      (smallFreeGen hC q ((GlobularPresheaf.whiskering n false).obj S) k x) =
      smallFreeGen hC q ((GlobularPresheaf.whiskering n false).obj S) k x := by
  change (underlyingMap (linearToWhisker hC q n S hS).hom).app k
    ((underlyingMap (whiskerToLinear hC q n S hS).hom).app k _) = _
  apply (congrArg ((underlyingMap (linearToWhisker hC q n S hS).hom).app k)
    (whiskerToLinear_gen hC q n S hS k x)).trans
  cases x with
  | base k x =>
    change (underlyingMap (linearToWhisker hC q n S hS).hom).app k
      (linOriginal hC q n S hS k x) = wBase hC q n S k x
    by_cases e : k = n
    · subst k
      erw [linOriginal_center, (underlyingMap (linearToWhisker hC q n S hS).hom).source_app,
        linearToWhisker_edge, wEdge_source]
    · have h : k < n := by omega
      erw [linOriginal_low _ _ _ _ _ _ h, linearToWhisker_low]
  | tip x =>
    change (underlyingMap (linearToWhisker hC q k S hS).hom).app k
      ((linearFree hC q k S).obj.underlying.target k (linEdge hC q k S x)) = _
    erw [(underlyingMap (linearToWhisker hC q k S hS).hom).target_app,
      linearToWhisker_edge, wEdge_target]
  | edge x => exact (Nat.not_succ_le_self n hk).elim

theorem whiskerLinear_top {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (S : GlobularPresheaf.{0}) (hS)
    (x : ((GlobularPresheaf.whiskering n false).obj S).underlying.Cell (n+1)) :
    (whiskerFree hC q n S).obj.underlying.Joined (n+1)
      ((underlyingMap (whiskerToLinear hC q n S hS ≫ linearToWhisker hC q n S hS).hom).app (n+1)
        (smallFreeGen hC q ((GlobularPresheaf.whiskering n false).obj S) (n+1) x))
      (smallFreeGen hC q ((GlobularPresheaf.whiskering n false).obj S) (n+1) x) := by
  change (whiskerFree hC q n S).obj.underlying.Joined (n+1)
    ((underlyingMap (linearToWhisker hC q n S hS).hom).app (n+1)
      ((underlyingMap (whiskerToLinear hC q n S hS).hom).app (n+1) _)) _
  have e := congrArg ((underlyingMap (linearToWhisker hC q n S hS).hom).app (n+1))
    (whiskerToLinear_gen hC q n S hS (n+1) x)
  apply (congrArg (fun z => (whiskerFree hC q n S).obj.underlying.Joined (n+1) z
    (smallFreeGen hC q ((GlobularPresheaf.whiskering n false).obj S) (n+1) x)) e).mpr
  cases x with
  | base k x =>
    change (whiskerFree hC q n S).obj.underlying.Joined (n+1)
      ((underlyingMap (linearToWhisker hC q n S hS).hom).app (n+1)
        (linOriginal hC q n S hS (n+1) x)) (wBase hC q n S (n+1) x)
    erw [linOriginal_high]
    simp only [map_compCell, linearToWhisker_edge, linearToWhisker_middle]
    exact (whiskerFree hC q n S).obj.compCell_cancel_left hC n
      (wEdge hC q n S (S.underlying.source n x)) (wBase hC q n S (n+1) x)
      (by rw [wEdge_source, wBase_source])
  | edge x =>
    change (whiskerFree hC q n S).obj.underlying.Joined (n+1)
      ((underlyingMap (linearToWhisker hC q n S hS).hom).app (n+1)
        (linEdge hC q n S x)) (wEdge hC q n S x)
    rw [linearToWhisker_edge]
    exact (whiskerFree hC q n S).obj.joined_refl hC _ _

end GlobularTheory.Model
namespace GlobularPresheaf

theorem disk_bounded (n k : ℕ) (h : n < k) : IsEmpty ((disk n).underlying.Cell k) := by
  constructor
  intro x
  change ULift (Globe.mk k ⟶ Globe.mk n) at x
  rcases x with ⟨x⟩
  change Globe.Face k n at x
  cases x with
  | id => omega
  | face h' ε => omega

end GlobularPresheaf
namespace Table

theorem bounded {l : ℕ} (T : Table l) (k : ℕ) (h : T.height < k) :
    IsEmpty (T.realize.underlying.Cell k) := by
  induction T with
  | globe n => exact GlobularPresheaf.disk_bounded n k h
  | @attach l T b j hl hr ih =>
    have hk : T.height < k := lt_of_le_of_lt (Nat.le_max_left _ _) h
    have hj : j < k := lt_of_le_of_lt (Nat.le_max_right _ _) h
    have H := (Shape.realization_pushout ⟨l,T⟩ b j hl hr).map
      ((evaluation Globeᵒᵖ (Type)).obj (op (Globe.mk k)))
    constructor
    intro x
    obtain ⟨y, _⟩ | ⟨y, _⟩ := Types.eq_or_eq_of_isPushout H x
    · exact (ih hk).false y
    · exact (GlobularPresheaf.disk_bounded j k hj).false y

end Table
namespace GlobularTheory.Model

theorem whiskerFree_bounded_hasFillers {C : GlobularTheory.{v}} (hC : C.IsCoherator)
    (q n : ℕ) (H : ExpansionContraction hC q (n+1))
    (S : Shape) (hS : S.height ≤ n+1) : (whiskerFree hC q n S.realize).obj.underlying.HasFillers := by
  have hb (k : ℕ) (hk : n+1 < k) : IsEmpty (S.realize.underlying.Cell k) :=
    S.2.bounded k (lt_of_le_of_lt hS hk)
  apply free_hasFillers_of_top_homotopy hC q n H
    (GlobularPresheaf.liftSmall.obj ((GlobularPresheaf.whiskering n false).obj S.realize))
    (fun k hk => ⟨fun x => (S.realize.underlying.whisker_bounded n false hb k hk).false x.down⟩)
    (linearFree hC q n S.realize) (smallFree_cofibrant hC q _)
    (linearFree_hasFillers hC q n S hS)
    (whiskerToLinear hC q n S.realize hb) (linearToWhisker hC q n S.realize hb)
  · intro k hk x
    exact whiskerLinear_low hC q n S.realize hb k hk x.down
  · intro x
    exact whiskerLinear_top hC q n S.realize hb x.down

end GlobularTheory.Model
end Grothendieck

end OAI
