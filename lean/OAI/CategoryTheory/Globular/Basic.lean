import OAI.CategoryTheory.Globular.Model

namespace OAI

universe u v w

namespace Grothendieck
namespace GlobularSet
@[simps]
def Hom.id (X : GlobularSet.{u}) : Hom X X where
  app _ := _root_.id
  source_app _ _ := rfl
  target_app _ _ := rfl

@[simps]
def Hom.comp {X Y Z : GlobularSet.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  app n x := g.app n (f.app n x)
  source_app n x := by rw [f.source_app, g.source_app]
  target_app n x := by rw [f.target_app, g.target_app]

instance : CategoryTheory.Category GlobularSet.{u} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := by ext; rfl
  comp_id _ := by ext; rfl
  assoc _ _ _ := by ext; rfl
@[simp]
theorem Hom.boundary_app {X Y : GlobularSet.{u}} (f : Hom X Y) (n) (x : X.Cell n) :
    f.boundaryMap n (X.boundary n x) = Y.boundary n (f.app n x) := by
  cases n with
  | zero => rfl
  | succ n => exact Subtype.ext (Prod.ext (f.source_app n x) (f.target_app n x))

def ExactBoundaryTest {X Y : GlobularSet.{u}} (f : Hom X Y) : Prop :=
  ∀ (n) (b : X.Boundary n) (y : Y.Cell n), Y.boundary n y = f.boundaryMap n b →
    ∃ x : X.Cell n, X.boundary n x = b ∧ Y.Joined n (f.app n x) y

theorem parallel_iff_boundary_eq (X : GlobularSet.{u}) (n) (x y : X.Cell n) :
    X.Parallel n x y ↔ X.boundary n x = X.boundary n y := by
  cases n with
  | zero => exact ⟨fun _ => rfl, fun _ => trivial⟩
  | succ n =>
    constructor
    · intro h
      exact Subtype.ext (Prod.ext h.1 h.2)
    · intro h
      have h' := congrArg Subtype.val h
      exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩

theorem ExactBoundaryTest.reflects_joined {X Y : GlobularSet.{u}} {f : Hom X Y}
    (hf : ExactBoundaryTest f) {n} {x y : X.Cell n} (hp : X.Parallel n x y)
    (h : Y.Joined n (f.app n x) (f.app n y)) : X.Joined n x y := by
  obtain ⟨h, hs, ht⟩ := h
  let b : X.Boundary (n + 1) := ⟨(x, y), hp⟩
  have hb : Y.boundary (n + 1) h = f.boundaryMap (n + 1) b := by
    exact Subtype.ext (Prod.ext hs ht)
  obtain ⟨z, hz, _⟩ := hf (n + 1) b h hb
  have hz' := congrArg Subtype.val hz
  exact ⟨z, congrArg Prod.fst hz', congrArg Prod.snd hz'⟩

@[simp]
theorem Hom.boundaryMap_comp {X Y Z : GlobularSet.{u}} (f : Hom X Y) (g : Hom Y Z)
    (n) (b : X.Boundary n) :
    (f.comp g).boundaryMap n b = g.boundaryMap n (f.boundaryMap n b) := by
  cases n <;> rfl

theorem ExactBoundaryTest.of_mutual_composites {X Y : GlobularSet.{u}}
    (i : Hom X Y) (r : Hom Y X)
    (hu : ExactBoundaryTest (i.comp r)) (hv : ExactBoundaryTest (r.comp i)) :
    ExactBoundaryTest i := by
  intro n b y hy
  have hb : X.boundary n (r.app n y) = (i.comp r).boundaryMap n b := by
    rw [← r.boundary_app, hy, Hom.boundaryMap_comp]
  obtain ⟨x, hx, h⟩ := hu n b (r.app n y) hb
  refine ⟨x, hx, hv.reflects_joined ?_ (i.map_joined h)⟩
  rw [parallel_iff_boundary_eq, ← i.boundary_app, hx, hy]

end GlobularSet

open CategoryTheory CategoryTheory.Limits Opposite

namespace GlobularTheory.Model
noncomputable def cellEquiv {C : GlobularTheory.{v}} (X : C.Model) (n : ℕ) :
    (disk C n ⟶ X) ≃ X.underlying.Cell n :=
  show (yoneda.obj (⟨Shape.globe n⟩ : C.Obj) ⟶ X.presheaf) ≃
    X.presheaf.obj (op (⟨Shape.globe n⟩ : C.Obj)) from yonedaEquiv

end GlobularTheory.Model

namespace GlobularTheory
theorem unit_source (C : GlobularTheory.{v}) (hC : C.IsCoherator) (n : ℕ) :
    C.comp (C.base (Shape.source n)) (C.unit hC n) = C.id (Shape.globe n) :=
  (Classical.choose_spec (hC.2 (C.unitPair n))).1

theorem unit_target (C : GlobularTheory.{v}) (hC : C.IsCoherator) (n : ℕ) :
    C.comp (C.base (Shape.target n)) (C.unit hC n) = C.id (Shape.globe n) :=
  (Classical.choose_spec (hC.2 (C.unitPair n))).2

end GlobularTheory

namespace GlobularTheory.Model
theorem eval_comp {C : GlobularTheory.{v}} (X : C.Model) {R S T : Shape}
    (f : C.Hom R S) (g : C.Hom S T) (x : X.presheaf.obj (op (⟨T⟩ : C.Obj))) :
    X.eval (C.comp f g) x = X.eval f (X.eval g x) := by
  exact ConcreteCategory.congr_hom
    (X.presheaf.map_comp (show (op (⟨T⟩ : C.Obj)) ⟶ op ⟨S⟩ from Quiver.Hom.op g)
      (show (op (⟨S⟩ : C.Obj)) ⟶ op ⟨R⟩ from Quiver.Hom.op f)) x

@[simp]
theorem eval_id {C : GlobularTheory.{v}} (X : C.Model) {S : Shape}
    (x : X.presheaf.obj (op (⟨S⟩ : C.Obj))) : X.eval (C.id S) x = x := by
  exact ConcreteCategory.congr_hom (X.presheaf.map_id (op (⟨S⟩ : C.Obj))) x
@[simp]
theorem unitCell_source {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (x : X.underlying.Cell n) : X.underlying.source n (X.unitCell hC n x) = x := by
  change X.presheaf.obj (op (⟨Shape.globe n⟩ : C.Obj)) at x
  change X.eval (C.base (Shape.source n)) (X.eval (C.unit hC n) x) = x
  rw [← eval_comp, C.unit_source, eval_id]

@[simp]
theorem unitCell_target {C : GlobularTheory.{v}} (X : C.Model) (hC : C.IsCoherator)
    (n : ℕ) (x : X.underlying.Cell n) : X.underlying.target n (X.unitCell hC n x) = x := by
  change X.presheaf.obj (op (⟨Shape.globe n⟩ : C.Obj)) at x
  change X.eval (C.base (Shape.target n)) (X.eval (C.unit hC n) x) = x
  rw [← eval_comp, C.unit_target, eval_id]

end GlobularTheory.Model
end Grothendieck

end OAI
