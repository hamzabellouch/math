import OAI.CategoryTheory.Globular.Fillers

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace GlobularTheory.Model

theorem sumTuple_ext {C : GlobularTheory.{v}} (X : C.Model)
    (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h)
    {x y : X.presheaf.obj (op (⟨S.attach b h hl hr⟩ : C.Obj))}
    (h₀ : X.eval (C.base (S.inl b h hl hr)) x = X.eval (C.base (S.inl b h hl hr)) y)
    (h₁ : X.eval (C.base (S.inr b h hl hr)) x = X.eval (C.base (S.inr b h hl hr)) y) : x = y :=
  Types.ext_of_isPullback (X.sums S b h hl hr) h₀ h₁

theorem map_compositionTuple {C : GlobularTheory.{v}} {X Y : C.Model} (f : X ⟶ Y)
    (n : ℕ) (a b : X.underlying.Cell (n+1))
    (hab : X.underlying.target n a = X.underlying.source n b) :
    f.app (op (⟨compositionShape n⟩ : C.Obj)) (X.compositionTuple n a b hab) =
      Y.compositionTuple n ((underlyingMap f).app (n+1) a) ((underlyingMap f).app (n+1) b)
        (by rw [← (underlyingMap f).target_app, ← (underlyingMap f).source_app, hab]) := by
  apply Y.sumTuple_ext (Shape.globe (n+1)) n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)
  · change Y.eval (C.base (compositionLeft n)) (f.app _ _) = Y.eval (C.base (compositionLeft n)) _
    rw [← map_eval, compositionTuple_left, compositionTuple_left]
    rfl
  · change Y.eval (C.base (compositionRight n)) (f.app _ _) = Y.eval (C.base (compositionRight n)) _
    rw [← map_eval, compositionTuple_right, compositionTuple_right]
    rfl

theorem map_compCell {C : GlobularTheory.{v}} {X Y : C.Model} (f : X ⟶ Y)
    (hC : C.IsCoherator) (n : ℕ) (a b : X.underlying.Cell (n+1))
    (hab : X.underlying.target n a = X.underlying.source n b) :
    (underlyingMap f).app (n+1) (X.compCell hC n a b hab) =
      Y.compCell hC n ((underlyingMap f).app (n+1) a) ((underlyingMap f).app (n+1) b)
        (by rw [← (underlyingMap f).target_app, ← (underlyingMap f).source_app, hab]) := by
  exact (map_eval f (C.composition hC n) (X.compositionTuple n a b hab)).trans
    (congrArg (Y.eval (C.composition hC n)) (map_compositionTuple f n a b hab))

noncomputable def tupleMap {C : GlobularTheory.{v}} (X : C.Model) (S : Shape)
    (t : X.presheaf.obj (op (⟨S⟩ : C.Obj))) : freeShape C S ⟶ X :=
  yonedaEquiv.symm t

@[simp] theorem tupleMap_app {C : GlobularTheory.{v}} (X : C.Model) (S : Shape)
    (t : X.presheaf.obj (op (⟨S⟩ : C.Obj))) (n : ℕ)
    (a : C.Hom (Shape.globe n) S) :
    (underlyingMap (X.tupleMap S t)).app n a = X.eval a t := rfl

theorem joined_of_parallel_expressions {C : GlobularTheory.{v}} (X : C.Model)
    (hC : C.IsCoherator) (S : Shape) (n : ℕ)
    (a b : (freeShape C S).underlying.Cell n)
    (hp : (freeShape C S).underlying.Parallel n a b)
    (t : X.presheaf.obj (op (⟨S⟩ : C.Obj))) :
    X.underlying.Joined n (X.eval a t) (X.eval b t) :=
  (underlyingMap (X.tupleMap S t)).map_joined (freeShape_joined C hC S n a b hp)

noncomputable def topCell (C : GlobularTheory.{v}) (n : ℕ) :
    (disk C n).underlying.Cell n := C.id (Shape.globe n)

@[simp] theorem tupleMap_topCell {C : GlobularTheory.{v}} (X : C.Model) (n : ℕ)
    (a : X.underlying.Cell n) :
    (underlyingMap (X.tupleMap (Shape.globe n) a)).app n (topCell C n) = a :=
  X.eval_id a

theorem compCell_left_unit {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (a : X.underlying.Cell (n+1)) :
    X.underlying.Joined (n+1)
      (X.compCell hC n (X.unitCell hC n (X.underlying.source n a)) a
        (X.unitCell_target hC n _)) a := by
  let D := disk C (n+1)
  let c := topCell C (n+1)
  let f : D ⟶ X := X.tupleMap (Shape.globe (n+1)) a
  have hf : (underlyingMap f).app (n+1) c = a := X.tupleMap_topCell (n+1) a
  let u := D.compCell hC n (D.unitCell hC n (D.underlying.source n c)) c
    (D.unitCell_target hC n _)
  have hp : D.underlying.Parallel (n+1) u c := by
    constructor <;> dsimp [u] <;> simp only [compCell_source, compCell_target, unitCell_source]
  have h := (underlyingMap f).map_joined
    (freeShape_joined C hC (Shape.globe (n+1)) (n+1) u c hp)
  simpa only [u, map_compCell f, map_unitCell f,
    (underlyingMap f).source_app, hf] using h

theorem compCell_right_unit {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (a : X.underlying.Cell (n+1)) :
    X.underlying.Joined (n+1)
      (X.compCell hC n a (X.unitCell hC n (X.underlying.target n a))
        (X.unitCell_source hC n _).symm) a := by
  let D := disk C (n+1)
  let c := topCell C (n+1)
  let f : D ⟶ X := X.tupleMap (Shape.globe (n+1)) a
  have hf : (underlyingMap f).app (n+1) c = a := X.tupleMap_topCell (n+1) a
  let u := D.compCell hC n c (D.unitCell hC n (D.underlying.target n c))
    (D.unitCell_source hC n _).symm
  have hp : D.underlying.Parallel (n+1) u c := by
    constructor <;> dsimp [u] <;> simp only [compCell_source, compCell_target, unitCell_target]
  have h := (underlyingMap f).map_joined
    (freeShape_joined C hC (Shape.globe (n+1)) (n+1) u c hp)
  simpa only [u, map_compCell f, map_unitCell f,
    (underlyingMap f).target_app, hf] using h

theorem compCell_inverse_right {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (a : X.underlying.Cell (n+1)) :
    X.underlying.Joined (n+1)
      (X.compCell hC n a (X.inverseCell hC n a) (X.inverseCell_source hC n a).symm)
      (X.unitCell hC n (X.underlying.source n a)) := by
  let D := disk C (n+1)
  let c := topCell C (n+1)
  let f : D ⟶ X := X.tupleMap (Shape.globe (n+1)) a
  have hf : (underlyingMap f).app (n+1) c = a := X.tupleMap_topCell (n+1) a
  let u := D.compCell hC n c (D.inverseCell hC n c) (D.inverseCell_source hC n c).symm
  let z := D.unitCell hC n (D.underlying.source n c)
  have hp : D.underlying.Parallel (n+1) u z := by
    constructor <;> dsimp [u, z] <;>
      simp only [compCell_source, compCell_target, inverseCell_target, unitCell_source, unitCell_target]
  have h := (underlyingMap f).map_joined
    (freeShape_joined C hC (Shape.globe (n+1)) (n+1) u z hp)
  simpa only [u, z, map_compCell f, map_unitCell f, map_inverseCell f,
    (underlyingMap f).source_app, hf] using h

theorem compCell_inverse_left {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (a : X.underlying.Cell (n+1)) :
    X.underlying.Joined (n+1)
      (X.compCell hC n (X.inverseCell hC n a) a (X.inverseCell_target hC n a))
      (X.unitCell hC n (X.underlying.target n a)) := by
  let D := disk C (n+1)
  let c := topCell C (n+1)
  let f : D ⟶ X := X.tupleMap (Shape.globe (n+1)) a
  have hf : (underlyingMap f).app (n+1) c = a := X.tupleMap_topCell (n+1) a
  let u := D.compCell hC n (D.inverseCell hC n c) c (D.inverseCell_target hC n c)
  let z := D.unitCell hC n (D.underlying.target n c)
  have hp : D.underlying.Parallel (n+1) u z := by
    constructor <;> dsimp [u, z] <;>
      simp only [compCell_source, compCell_target, inverseCell_source, unitCell_source, unitCell_target]
  have h := (underlyingMap f).map_joined
    (freeShape_joined C hC (Shape.globe (n+1)) (n+1) u z hp)
  simpa only [u, z, map_compCell f, map_unitCell f, map_inverseCell f,
    (underlyingMap f).target_app, hf] using h

end GlobularTheory.Model
end Grothendieck

namespace Grothendieck.GlobularSet

theorem Hom.boundaryMap_id (X : GlobularSet.{u}) (n : ℕ) (b : X.Boundary n) :
    (Hom.id X).boundaryMap n b = b := by
  cases n with
  | zero =>
    change (PUnit.unit : PUnit) = b
    exact Subsingleton.elim _ _
  | succ n => exact Subtype.ext rfl

theorem HasFillers.joined {X : GlobularSet.{u}} (hX : X.HasFillers)
    {n : ℕ} {a b : X.Cell n} (hp : X.Parallel n a b) : X.Joined n a b := by
  obtain ⟨z, hz⟩ := hX (n+1) ⟨(a,b), hp⟩
  exact ⟨z, congrArg (fun x => x.1.1) hz, congrArg (fun x => x.1.2) hz⟩

theorem HasFillers.retract {X Y : GlobularSet.{u}} (hY : Y.HasFillers)
    (i : Hom X Y) (r : Hom Y X) (hir : i.comp r = Hom.id X) : X.HasFillers := by
  intro n b
  obtain ⟨y, hy⟩ := hY n (i.boundaryMap n b)
  refine ⟨r.app n y, ?_⟩
  rw [← r.boundary_app, hy, ← Hom.boundaryMap_comp, hir, Hom.boundaryMap_id]

theorem hasFillers_of_endpoint_factorization {X Y P : GlobularSet.{u}}
    (hX : X.HasFillers) (i : Hom X Y) (r : Hom Y X) (h : Hom Y P)
    (p₀ p₁ : Hom P Y) (hh₀ : h.comp p₀ = Hom.id Y)
    (hh₁ : h.comp p₁ = r.comp i) (hp₁ : LiftsBoundaries p₁) : Y.HasFillers := by
  intro n b
  obtain ⟨x, hx⟩ := hX n (r.boundaryMap n b)
  have hb : Y.boundary n (i.app n x) = p₁.boundaryMap n (h.boundaryMap n b) := by
    rw [← i.boundary_app, hx, ← Hom.boundaryMap_comp, ← Hom.boundaryMap_comp, hh₁]
  obtain ⟨z, hz, _⟩ := hp₁ n (h.boundaryMap n b) (i.app n x) hb
  refine ⟨p₀.app n z, ?_⟩
  rw [← p₀.boundary_app, hz, ← Hom.boundaryMap_comp, hh₀, Hom.boundaryMap_id]

def LiftsSource {X Y : GlobularSet.{u}} (f : Hom X Y) (n : ℕ) : Prop :=
  ∀ (x : X.Cell n) (y : Y.Cell (n+1)), Y.source n y = f.app n x →
    ∃ z : X.Cell (n+1), X.source n z = x ∧ f.app (n+1) z = y

theorem liftsBoundary_of_contractible {X Y : GlobularSet.{u}} (f : Hom X Y)
    (hX : X.HasFillers) (hY : Y.HasFillers) (n : ℕ) (hf : LiftsSource f n)
    (b : X.Boundary n) (y : Y.Cell n) (hy : Y.boundary n y = f.boundaryMap n b) :
    ∃ x : X.Cell n, X.boundary n x = b ∧ f.app n x = y := by
  obtain ⟨x, hx⟩ := hX n b
  have hp : Y.Parallel n (f.app n x) y := by
    rw [parallel_iff_boundary_eq, ← f.boundary_app, hx, hy]
  obtain ⟨c, hc₀, hc₁⟩ := hY.joined hp
  obtain ⟨d, hd₀, hd⟩ := hf x c hc₀
  refine ⟨X.target n d, ?_, ?_⟩
  · have h := (parallel_iff_boundary_eq X n (X.source n d) (X.target n d)).1
      (Joined.parallel ⟨d, rfl, rfl⟩)
    rw [hd₀, hx] at h
    exact h.symm
  · rw [f.target_app, hd, hc₁]

end Grothendieck.GlobularSet

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite

namespace Shape

theorem attach_seam (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h)
    {k : ℕ} (hk : k < h) :
    (S.attach b h hl hr).seam hk = face hk true ≫ S.inr b h hl hr := rfl

end Shape

namespace GlobularTheory

def tripleShape (n : ℕ) : Shape :=
  (compositionShape n).attach n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

noncomputable def tripleFirst (n : ℕ) : Shape.globe (n+1) ⟶ tripleShape n :=
  compositionLeft n ≫ (compositionShape n).inl n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

noncomputable def tripleMiddle (n : ℕ) : Shape.globe (n+1) ⟶ tripleShape n :=
  compositionRight n ≫ (compositionShape n).inl n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

noncomputable def tripleLast (n : ℕ) : Shape.globe (n+1) ⟶ tripleShape n :=
  (compositionShape n).inr n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

theorem triple_first_middle (n : ℕ) :
    Shape.target n ≫ tripleFirst n = Shape.source n ≫ tripleMiddle n := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ (compositionShape n).inl n (n+1)
      (Nat.lt_succ_self n) (Nat.lt_succ_self n)) (composition_seam n)).trans
        (Category.assoc _ _ _))

theorem triple_middle_last (n : ℕ) :
    Shape.target n ≫ tripleMiddle n = Shape.source n ≫ tripleLast n := by
  have h := Shape.seam_inl (compositionShape n) n (n+1)
    (Nat.lt_succ_self n) (Nat.lt_succ_self n)
  change (Shape.target n ≫ compositionRight n) ≫ _ = Shape.source n ≫ _ at h
  exact (Category.assoc _ _ _).symm.trans h

namespace Model

noncomputable def tripleTuple {C : GlobularTheory.{v}} (X : C.Model) (n : ℕ)
    (a b c : X.underlying.Cell (n+1))
    (hab : X.underlying.target n a = X.underlying.source n b)
    (hbc : X.underlying.target n b = X.underlying.source n c) :
    X.presheaf.obj (op (⟨tripleShape n⟩ : C.Obj)) :=
  X.sumTuple (compositionShape n) n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)
    (X.compositionTuple n a b hab) c (by
      change X.eval (C.base (Shape.target n ≫ compositionRight n)) _ = _
      rw [C.base_comp, eval_comp, compositionTuple_right]
      exact hbc)

@[simp] theorem tripleTuple_first {C : GlobularTheory.{v}} (X : C.Model) (n : ℕ)
    (a b c : X.underlying.Cell (n+1))
    (hab : X.underlying.target n a = X.underlying.source n b)
    (hbc : X.underlying.target n b = X.underlying.source n c) :
    X.eval (C.base (tripleFirst n)) (X.tripleTuple n a b c hab hbc) = a := by
  let j : compositionShape n ⟶ tripleShape n := (compositionShape n).inl n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)
  let t := X.tripleTuple n a b c hab hbc
  change X.eval (C.base (compositionLeft n ≫ j)) t = a
  rw [C.base_comp, eval_comp]
  have hj : X.eval (C.base j) t = X.compositionTuple n a b hab :=
    X.sumTuple_left _ _ _ _ _ _ _ _
  rw [hj, compositionTuple_left]

@[simp] theorem tripleTuple_middle {C : GlobularTheory.{v}} (X : C.Model) (n : ℕ)
    (a b c : X.underlying.Cell (n+1))
    (hab : X.underlying.target n a = X.underlying.source n b)
    (hbc : X.underlying.target n b = X.underlying.source n c) :
    X.eval (C.base (tripleMiddle n)) (X.tripleTuple n a b c hab hbc) = b := by
  let j : compositionShape n ⟶ tripleShape n := (compositionShape n).inl n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)
  let t := X.tripleTuple n a b c hab hbc
  change X.eval (C.base (compositionRight n ≫ j)) t = b
  rw [C.base_comp, eval_comp]
  have hj : X.eval (C.base j) t = X.compositionTuple n a b hab :=
    X.sumTuple_left _ _ _ _ _ _ _ _
  rw [hj, compositionTuple_right]

@[simp] theorem tripleTuple_last {C : GlobularTheory.{v}} (X : C.Model) (n : ℕ)
    (a b c : X.underlying.Cell (n+1))
    (hab : X.underlying.target n a = X.underlying.source n b)
    (hbc : X.underlying.target n b = X.underlying.source n c) :
    X.eval (C.base (tripleLast n)) (X.tripleTuple n a b c hab hbc) = c :=
  X.sumTuple_right _ _ _ _ _ _ _ _

theorem compCell_assoc {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (a b c : X.underlying.Cell (n+1))
    (hab : X.underlying.target n a = X.underlying.source n b)
    (hbc : X.underlying.target n b = X.underlying.source n c) :
    X.underlying.Joined (n+1)
      (X.compCell hC n (X.compCell hC n a b hab) c (by rw [compCell_target, hbc]))
      (X.compCell hC n a (X.compCell hC n b c hbc) (by rw [compCell_source, hab])) := by
  let D := freeShape C (tripleShape n)
  let A : D.underlying.Cell (n+1) := C.base (tripleFirst n)
  let B : D.underlying.Cell (n+1) := C.base (tripleMiddle n)
  let E : D.underlying.Cell (n+1) := C.base (tripleLast n)
  have hAB : D.underlying.target n A = D.underlying.source n B := by
    change C.comp (C.base (Shape.target n)) (C.base (tripleFirst n)) =
      C.comp (C.base (Shape.source n)) (C.base (tripleMiddle n))
    rw [← C.base_comp, ← C.base_comp, triple_first_middle]
  have hBE : D.underlying.target n B = D.underlying.source n E := by
    change C.comp (C.base (Shape.target n)) (C.base (tripleMiddle n)) =
      C.comp (C.base (Shape.source n)) (C.base (tripleLast n))
    rw [← C.base_comp, ← C.base_comp, triple_middle_last]
  let f : D ⟶ X := X.tupleMap (tripleShape n) (X.tripleTuple n a b c hab hbc)
  have hfA : (underlyingMap f).app (n+1) A = a := X.tripleTuple_first n a b c hab hbc
  have hfB : (underlyingMap f).app (n+1) B = b := X.tripleTuple_middle n a b c hab hbc
  have hfE : (underlyingMap f).app (n+1) E = c := X.tripleTuple_last n a b c hab hbc
  let u := D.compCell hC n (D.compCell hC n A B hAB) E (by rw [compCell_target, hBE])
  let z := D.compCell hC n A (D.compCell hC n B E hBE) (by rw [compCell_source, hAB])
  have hp : D.underlying.Parallel (n+1) u z := by
    constructor <;> dsimp [u, z] <;> simp only [compCell_source, compCell_target]
  have h := (underlyingMap f).map_joined (freeShape_joined C hC (tripleShape n) (n+1) u z hp)
  simpa only [u, z, map_compCell f, hfA, hfB, hfE] using h

end Model
end GlobularTheory
end Grothendieck

end OAI
