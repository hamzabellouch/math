import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionCartesian
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic

namespace OAI

section

/-!
# Removing maximal new objects

The finite induction in the couniversality proof splits the poset into two
full sieves by deleting distinct maximal objects outside the old sieve.
The restricted sieves retain the right adjoint.
-/

namespace Thomason.Construction

universe u

variable {E : Type u} [PartialOrder E] {A : Set E}

/-- In a finite nonempty set with no greatest element, there are two distinct
maximal elements. -/
theorem two_maximal_of_no_greatest {S : Set E} (hS : S.Finite) (hne : S.Nonempty)
    (hgreatest : ¬ ∃ x, x ∈ S ∧ ∀ y ∈ S, y ≤ x) :
    ∃ x y, Maximal (· ∈ S) x ∧ Maximal (· ∈ S) y ∧ x ≠ y := by
  classical
  obtain ⟨x, hx⟩ := hS.exists_maximal hne
  by_contra h
  have hall : ∀ y, Maximal (· ∈ S) y → x = y := by
    intro y hy
    by_contra hxy
    exact h ⟨x, y, hx, hy, hxy⟩
  apply hgreatest
  refine ⟨x, hx.prop, ?_⟩
  intro z hz
  obtain ⟨y, hzy, hy⟩ := hS.exists_le_maximal hz
  exact hall y hy ▸ hzy

namespace SieveRetraction

variable (R : SieveRetraction A)

include R in
/-- Maximality in the complement of a sieve implies maximality in the ambient
poset; a morphism from a new object to an old object is impossible. -/
theorem maximal_complement_is_maximal {x : E} (hx : Maximal (· ∉ A) x) :
    Maximal (fun _ : E => True) x := by
  refine ⟨trivial, ?_⟩
  intro y _ hxy
  have hy : y ∉ A := fun hy => hx.prop (R.lower hxy hy)
  exact hx.le_of_ge hy hxy

/-- Deleting a maximal object leaves a sieve. -/
theorem delete_maximal_isLowerSet {x : E} (hx : Maximal (fun _ : E => True) x) :
    IsLowerSet {e : E | e ≠ x} := by
  intro a b hab hb ha
  subst b
  exact hb (le_antisymm (hx.le_of_ge trivial hab) hab)

/-- Restriction to any full subposet containing the old part preserves the
right-adjoint retraction. Downward closure of the subposet is not needed. -/
def restrict (S : Set E) (hAS : A ⊆ S) :
    SieveRetraction {e : S | (e : E) ∈ A} where
  lower := by
    intro a b hab hb
    exact R.lower hab hb
  rightAdjoint :=
    { toFun := fun e => ⟨⟨R.projection e, hAS (R.projection_mem e)⟩,
        R.projection_mem e⟩
      monotone' := fun _ _ h => R.projection.monotone h }
  adjunction a e := R.adjunction ⟨a.val.val, a.property⟩ e

include R in
/-- The two-sieve cover used by the finite couniversality induction. -/
theorem finite_two_sieve_cover [Finite E]
    (hne : (Aᶜ).Nonempty) (hgreatest : ¬ ∃ x, GreatestNew (A := A) x) :
    ∃ x y, x ∉ A ∧ y ∉ A ∧ x ≠ y ∧
      IsLowerSet {e : E | e ≠ x} ∧ IsLowerSet {e : E | e ≠ y} ∧
      A ⊆ {e : E | e ≠ x} ∧ A ⊆ {e : E | e ≠ y} ∧
      (∀ e : E, e ≠ x ∨ e ≠ y) := by
  classical
  have hng : ¬ ∃ x, x ∈ Aᶜ ∧ ∀ y ∈ Aᶜ, y ≤ x := by
    rintro ⟨x, hx, hg⟩
    exact hgreatest ⟨x, hx, hg⟩
  obtain ⟨x, y, hx, hy, hxy⟩ :=
    two_maximal_of_no_greatest (Set.toFinite Aᶜ) hne hng
  refine ⟨x, y, hx.prop, hy.prop, hxy,
    delete_maximal_isLowerSet (R.maximal_complement_is_maximal hx),
    delete_maximal_isLowerSet (R.maximal_complement_is_maximal hy), ?_, ?_, ?_⟩
  · intro a ha hax
    exact hx.prop (hax ▸ ha)
  · intro a ha hay
    exact hy.prop (hay ▸ ha)
  · intro e
    by_cases he : e = x
    · exact Or.inr (fun hey => hxy (he.symm.trans hey))
    · exact Or.inl he

end SieveRetraction
end Thomason.Construction

end

section

/-!
# Small strict globular omega-categories

We use the standard one-sorted description: an identity extension of a cell
is the same element of the carrier. Its `n`-source and `n`-target are
endomaps, and composition is defined precisely on matching boundaries.
Every element has finite dimension. This is the convention for the strict
omega-categories in Steiner, *Omega-categories and chain complexes* (2004),
Section 2.

`false` denotes source and `true` denotes target. The finite dimensional
subcategories below impose a uniform dimension bound on these same objects.
-/

namespace Thomason.Construction

open CategoryTheory

universe u v

/-- A strict globular omega-category with identities represented by the same
cell at all higher dimensions. All compositions, units and interchange laws
are strict equalities. -/
structure StrictOmegaCategory where
  Cell : Type u
  face : Bool → ℕ → Cell → Cell
  globular (a b : Bool) (m n : ℕ) (x : Cell) :
    face a m (face b n x) = if m < n then face a m x else face b n x
  comp (n : ℕ) (x y : Cell) (h : face true n x = face false n y) : Cell
  source_comp (n : ℕ) (x y : Cell) (h) :
    face false n (comp n x y h) = face false n x
  target_comp (n : ℕ) (x y : Cell) (h) :
    face true n (comp n x y h) = face true n y
  face_comp (a : Bool) (m n : ℕ) (hnm : n < m) (x y : Cell)
      (h : face true n x = face false n y)
      (h' : face true n (face a m x) = face false n (face a m y)) :
    face a m (comp n x y h) = comp n (face a m x) (face a m y) h'
  left_unit (n : ℕ) (x : Cell) (h : face true n (face false n x) = face false n x) :
    comp n (face false n x) x h = x
  right_unit (n : ℕ) (x : Cell) (h : face true n x = face false n (face true n x)) :
    comp n x (face true n x) h = x
  assoc (n : ℕ) (x y z : Cell)
      (hxy : face true n x = face false n y)
      (hyz : face true n y = face false n z)
      (hl : face true n (comp n x y hxy) = face false n z)
      (hr : face true n x = face false n (comp n y z hyz)) :
    comp n (comp n x y hxy) z hl = comp n x (comp n y z hyz) hr
  interchange (m n : ℕ) (hmn : m < n) (a b c d : Cell)
      (hab : face true m a = face false m b)
      (hcd : face true m c = face false m d)
      (hac : face true n a = face false n c)
      (hbd : face true n b = face false n d)
      (hl : face true n (comp m a b hab) = face false n (comp m c d hcd))
      (hr : face true m (comp n a c hac) = face false m (comp n b d hbd)) :
    comp n (comp m a b hab) (comp m c d hcd) hl =
      comp m (comp n a c hac) (comp n b d hbd) hr
  finite_dimension (x : Cell) : ∃ n, face false n x = x ∧ face true n x = x

namespace StrictOmegaCategory

instance : CoeSort StrictOmegaCategory.{u} (Type u) := ⟨Cell⟩

abbrev source (C : StrictOmegaCategory) (n : ℕ) : C → C := C.face false n
abbrev target (C : StrictOmegaCategory) (n : ℕ) : C → C := C.face true n

/-- A strict functor preserves both boundaries and every defined composition. -/
@[ext]
structure Hom (C : StrictOmegaCategory.{u}) (D : StrictOmegaCategory.{v}) where
  toFun : C → D
  map_face (a : Bool) (n : ℕ) (x : C) : toFun (C.face a n x) = D.face a n (toFun x)
  map_comp (n : ℕ) (x y : C) (h : C.target n x = C.source n y)
      (h' : D.target n (toFun x) = D.source n (toFun y)) :
    toFun (C.comp n x y h) = D.comp n (toFun x) (toFun y) h'

instance {C : StrictOmegaCategory.{u}} {D : StrictOmegaCategory.{v}} :
    CoeFun (Hom C D) (fun _ => C → D) := ⟨Hom.toFun⟩

namespace Hom

def id (C : StrictOmegaCategory) : Hom C C where
  toFun := _root_.id
  map_face _ _ _ := rfl
  map_comp _ _ _ _ _ := rfl

def comp {C D E : StrictOmegaCategory} (f : Hom C D) (g : Hom D E) : Hom C E where
  toFun x := g (f x)
  map_face a n x := by rw [f.map_face, g.map_face]
  map_comp n x y h h' := by
    have hf : D.target n (f x) = D.source n (f y) := by
      exact (f.map_face true n x).symm.trans
        ((congrArg f.toFun h).trans (f.map_face false n y))
    rw [f.map_comp n x y h hf, g.map_comp n (f x) (f y) hf h']

@[simp] theorem id_apply (C : StrictOmegaCategory) (x : C) : id C x = x := rfl
@[simp] theorem comp_apply {C D E : StrictOmegaCategory} (f : Hom C D) (g : Hom D E)
    (x : C) : comp f g x = g (f x) := rfl

end Hom

instance : CategoryTheory.Category StrictOmegaCategory.{u} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := by ext; rfl
  comp_id _ := by ext; rfl
  assoc _ _ _ := by ext; rfl

/-- A cell has dimension at most `n` precisely when its `n`-boundaries are
itself. Higher identity extensions require no extra cell data. -/
def DimensionLE (C : StrictOmegaCategory) (n : ℕ) (x : C) : Prop :=
  C.source n x = x ∧ C.target n x = x

@[simp]
theorem face_face_same (C : StrictOmegaCategory) (a b : Bool) (n : ℕ) (x : C) :
    C.face a n (C.face b n x) = C.face b n x := by
  simpa only [Nat.lt_irrefl, ite_false] using C.globular a b n n x

theorem face_dimensionLE (C : StrictOmegaCategory) (a : Bool) (n : ℕ) (x : C) :
    C.DimensionLE n (C.face a n x) :=
  ⟨C.face_face_same false a n x, C.face_face_same true a n x⟩

theorem dimensionLE_mono (C : StrictOmegaCategory) {m n : ℕ} (hmn : m ≤ n)
    {x : C} (hx : C.DimensionLE m x) : C.DimensionLE n x := by
  have hf (a : Bool) : C.face a n x = x := by
    rw [← hx.1]
    simpa only [show ¬n < m from Nat.not_lt.mpr hmn, ite_false] using
      C.globular a false n m x
  exact ⟨hf false, hf true⟩

theorem Hom.dimensionLE {C D : StrictOmegaCategory} (f : Hom C D)
    {n : ℕ} {x : C} (hx : C.DimensionLE n x) : D.DimensionLE n (f x) := by
  constructor
  · exact (f.map_face false n x).symm.trans (congrArg f.toFun hx.1)
  · exact (f.map_face true n x).symm.trans (congrArg f.toFun hx.2)

/-- Composing along a strictly lower boundary preserves a dimension bound. -/
theorem dimensionLE_comp (C : StrictOmegaCategory) {n m : ℕ} (hnm : n < m)
    {x y : C} (hx : C.DimensionLE m x) (hy : C.DimensionLE m y)
    (h : C.target n x = C.source n y) : C.DimensionLE m (C.comp n x y h) := by
  constructor
  · have h' : C.target n (C.source m x) = C.source n (C.source m y) := by
      rw [hx.1, hy.1]; exact h
    change C.face false m (C.comp n x y h) = C.comp n x y h
    have hx' : C.face false m x = x := hx.1
    have hy' : C.face false m y = y := hy.1
    simpa only [hx', hy'] using C.face_comp false m n hnm x y h h'
  · have h' : C.target n (C.target m x) = C.source n (C.target m y) := by
      rw [hx.2, hy.2]; exact h
    change C.face true m (C.comp n x y h) = C.comp n x y h
    have hx' : C.face true m x = x := hx.2
    have hy' : C.face true m y = y := hy.2
    simpa only [hx', hy'] using C.face_comp true m n hnm x y h h'

/-- Strict `n`-categories are the full subcategory with a uniform dimension
bound; no invertibility condition is imposed. -/
def IsTruncated (C : StrictOmegaCategory) (n : ℕ) : Prop :=
  ∀ x : C, C.DimensionLE n x

def Truncated (n : ℕ) := {C : StrictOmegaCategory.{u} // C.IsTruncated n}

instance (n : ℕ) : CategoryTheory.Category (Truncated.{u} n) where
  Hom C D := Hom C.val D.val
  id C := Hom.id C.val
  comp := Hom.comp
  id_comp _ := by ext; rfl
  comp_id _ := by ext; rfl
  assoc _ _ _ := by ext; rfl

/-- The fully faithful inclusion of strict `n`-categories into omega-categories. -/
def inclusion (n : ℕ) : Truncated.{u} n ⥤ StrictOmegaCategory.{u} where
  obj C := C.val
  map f := f

end StrictOmegaCategory
end Thomason.Construction

end

section

/-!
# Actual full strict subcategories on sets of objects

Membership means that both zero-dimensional boundaries lie in the chosen
set. The inherited globular operations are closed on these cells, without
assuming the set is a sieve or cosieve.
-/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory

universe u

variable (C : StrictOmegaCategory.{u}) (S : Set C)

/-- All cells whose two object boundaries lie in the specified set. -/
def FullCell (x : C) : Prop := C.source 0 x ∈ S ∧ C.target 0 x ∈ S

theorem fullCell_face {x : C} (hx : C.FullCell S x) (a : Bool) (n : ℕ) :
    C.FullCell S (C.face a n x) := by
  cases n with
  | zero =>
    change C.face false 0 (C.face a 0 x) ∈ S ∧ C.face true 0 (C.face a 0 x) ∈ S
    simp only [C.face_face_same]
    cases a
    · exact ⟨hx.1, hx.1⟩
    · exact ⟨hx.2, hx.2⟩
  | succ n =>
    change C.face false 0 (C.face a (n + 1) x) ∈ S ∧ C.face true 0 (C.face a (n + 1) x) ∈ S
    simpa only [FullCell, source, target, C.globular, Nat.zero_lt_succ, ite_true] using hx

/-- A positive-dimensional composition has the object boundaries of its
first factor. This follows directly from globularity. -/
theorem zero_face_comp_succ (a : Bool) (n : ℕ) (x y : C)
    (hxy : C.target (n + 1) x = C.source (n + 1) y) :
    C.face a 0 (C.comp (n + 1) x y hxy) = C.face a 0 x := by
  have hleft := C.globular a false 0 (n + 1) (C.comp (n + 1) x y hxy)
  have hright := C.globular a false 0 (n + 1) x
  simp only [Nat.zero_lt_succ, ite_true] at hleft hright
  exact hleft.symm.trans ((congrArg (C.face a 0) (C.source_comp (n + 1) x y hxy)).trans hright)

theorem fullCell_comp {x y : C} (hx : C.FullCell S x) (hy : C.FullCell S y)
    (n : ℕ) (hxy : C.target n x = C.source n y) : C.FullCell S (C.comp n x y hxy) := by
  cases n with
  | zero =>
    change C.face false 0 (C.comp 0 x y hxy) ∈ S ∧ C.face true 0 (C.comp 0 x y hxy) ∈ S
    rw [C.source_comp, C.target_comp]
    exact ⟨hx.1, hy.2⟩
  | succ n =>
    change C.face false 0 (C.comp (n + 1) x y hxy) ∈ S ∧
      C.face true 0 (C.comp (n + 1) x y hxy) ∈ S
    simpa only [FullCell, source, target, C.zero_face_comp_succ] using hx

/-- The full strict omega-subcategory on a set of object cells. -/
def fullOn : StrictOmegaCategory.{u} where
  Cell := {x : C // C.FullCell S x}
  face a n x := ⟨C.face a n x.val, C.fullCell_face S x.property a n⟩
  globular a b m n x := by
    apply Subtype.ext
    exact (C.globular a b m n x.val).trans (by split_ifs <;> rfl)
  comp n x y hxy := ⟨C.comp n x.val y.val (congrArg Subtype.val hxy),
    C.fullCell_comp S x.property y.property n _⟩
  source_comp n x y hxy := Subtype.ext (C.source_comp n x.val y.val _)
  target_comp n x y hxy := Subtype.ext (C.target_comp n x.val y.val _)
  face_comp a m n hnm x y hxy h' := Subtype.ext (C.face_comp a m n hnm x.val y.val _ _)
  left_unit n x hxy := Subtype.ext (C.left_unit n x.val _)
  right_unit n x hxy := Subtype.ext (C.right_unit n x.val _)
  assoc n x y z hxy hyz hl hr := Subtype.ext (C.assoc n x.val y.val z.val _ _ _ _)
  interchange m n hmn a b c d hab hcd hac hbd hl hr :=
    Subtype.ext (C.interchange m n hmn a.val b.val c.val d.val _ _ _ _ _ _)
  finite_dimension x := by
    obtain ⟨n, hs, ht⟩ := C.finite_dimension x.val
    exact ⟨n, Subtype.ext hs, Subtype.ext ht⟩

/-- The inclusion preserves all strict compositions and faces. -/
def fullInclusion : C.fullOn S ⟶ C where
  toFun x := x.val
  map_face _ _ _ := rfl
  map_comp _ _ _ _ _ := rfl

/-- Full subcategories preserve any bound on dimension. -/
theorem fullOn_isTruncated {n : ℕ} (hC : C.IsTruncated n) : (C.fullOn S).IsTruncated n := by
  intro x
  exact ⟨Subtype.ext (hC x.val).1, Subtype.ext (hC x.val).2⟩

/-- Restrict a strict functor that sends the selected objects to selected objects. -/
def fullMap {D : StrictOmegaCategory.{u}} (T : Set D) (f : C ⟶ D)
    (h : ∀ x ∈ S, f.toFun x ∈ T) : C.fullOn S ⟶ D.fullOn T where
  toFun x := ⟨f.toFun x.val, by
    constructor
    · change D.face false 0 (f.toFun x.val) ∈ T
      rw [← f.map_face]
      exact h _ x.property.1
    · change D.face true 0 (f.toFun x.val) ∈ T
      rw [← f.map_face]
      exact h _ x.property.2⟩
  map_face a n x := Subtype.ext (f.map_face a n x.val)
  map_comp n x y hxy h' := Subtype.ext (f.map_comp n x.val y.val _ _)

/-- Restriction commutes strictly with the inclusions. -/
theorem fullMap_inclusion {D : StrictOmegaCategory.{u}} (T : Set D) (f : C ⟶ D)
    (h : ∀ x ∈ S, f.toFun x ∈ T) :
    C.fullMap S T f h ≫ D.fullInclusion T = C.fullInclusion S ≫ f := by
  apply Hom.ext
  rfl

/-- Full-subcategory inclusions are monomorphisms of actual strict categories. -/
instance fullInclusion_mono : Mono (C.fullInclusion S) where
  right_cancellation := by
    intro Z f g he
    apply Hom.ext
    funext x
    apply Subtype.ext
    exact congrArg (fun k : Z ⟶ C => k.toFun x) he

end Thomason.Construction.StrictOmegaCategory

end

section

/-! # Small formal cells for strict omega-category colimits

Formal cells are generated by diagram cells, faces and compositions. A
composition is admitted precisely when its boundary equation holds in
every cocone. Quotienting by equality in every cocone will therefore allow
exactly all compositions required in the colimit. This uses a small term
type; the collection of testing cocones occurs only in propositions.
-/

namespace Thomason.Construction.StrictOmegaCategory.ColimitConstruction

open CategoryTheory CategoryTheory.Limits

variable {J : Type} [Category.{0} J] (F : J ⥤ StrictOmegaCategory.{0})

/-- Finite expressions over the cells of the small diagram. -/
inductive Term where
  | gen (j : J) (x : F.obj j)
  | face (a : Bool) (n : ℕ) (x : Term)
  | comp (n : ℕ) (x y : Term)

namespace Term

variable {F}

/-- Evaluation in any given cocone. On inadmissible expressions the first
factor supplies a harmless totalization; admitted terms never use it. -/
noncomputable def eval (s : Cocone F) (t : Term F) : s.pt := by
  classical
  exact t.rec (fun j x => (s.ι.app j).toFun x)
    (fun a n _ x => s.pt.face a n x)
    (fun n _ _ x y => if he : s.pt.target n x = s.pt.source n y then
      s.pt.comp n x y he else x)

@[simp] theorem eval_gen (s : Cocone F) (j : J) (x : F.obj j) :
    eval s (.gen j x) = (s.ι.app j).toFun x := rfl

@[simp] theorem eval_face (s : Cocone F) (a : Bool) (n : ℕ) (x : Term F) :
    eval s (.face a n x) = s.pt.face a n (eval s x) := rfl

theorem eval_comp (s : Cocone F) (n : ℕ) (x y : Term F)
    (he : s.pt.target n (eval s x) = s.pt.source n (eval s y)) :
    eval s (.comp n x y) = s.pt.comp n (eval s x) (eval s y) he := by
  classical
  exact dite_eq_left he

end Term

/-- Admissibility uses only boundary equations forced by the diagram. -/
inductive Good : Term F → Prop where
  | gen (j : J) (x : F.obj j) : Good (.gen j x)
  | face (a : Bool) (n : ℕ) {x : Term F} : Good x → Good (.face a n x)
  | comp (n : ℕ) {x y : Term F} : Good x → Good y →
      (∀ s : Cocone F, s.pt.target n (x.eval s) = s.pt.source n (y.eval s)) →
      Good (.comp n x y)

/-- Each admitted finite expression has one finite dimension bound valid
in every cocone. In particular the quotient will be an omega-category. -/
theorem Good.uniformDimension {t : Term F} (ht : Good F t) :
    ∃ n, ∀ s : Cocone F, s.pt.DimensionLE n (t.eval s) := by
  induction ht with
  | gen j x =>
    obtain ⟨n, hn⟩ := (F.obj j).finite_dimension x
    exact ⟨n, fun s => (s.ι.app j).dimensionLE hn⟩
  | face a n ht ih =>
    exact ⟨n, fun s => s.pt.face_dimensionLE a n _⟩
  | @comp n x y hx hy he ihx ihy =>
    obtain ⟨p, hp⟩ := ihx
    obtain ⟨q, hq⟩ := ihy
    refine ⟨max (n+1) (max p q), fun s => ?_⟩
    rw [Term.eval_comp s n x y (he s)]
    exact s.pt.dimensionLE_comp (by omega)
      (s.pt.dimensionLE_mono (by omega) (hp s))
      (s.pt.dimensionLE_mono (by omega) (hq s)) (he s)

/-- The small carrier before quotienting. -/
abbrev Admitted := {t : Term F // Good F t}

/-- Equality forced by every strict cocone on the diagram. -/
def Rel (x y : Admitted F) : Prop := ∀ s : Cocone F, x.val.eval s = y.val.eval s

instance semanticSetoid : Setoid (Admitted F) where
  r := Rel F
  iseqv := ⟨fun _ _ => rfl, fun he s => (he s).symm,
    fun he hf s => (he s).trans (hf s)⟩

/-- A small quotient: large cocones occur only in its defining proposition. -/
abbrev Cell := Quotient (semanticSetoid F)

namespace Cell

variable {F}

/-- Interpret a quotient cell in any cocone. -/
noncomputable def eval (s : Cocone F) : Cell F → s.pt :=
  Quotient.lift (fun x => x.val.eval s) (fun _ _ he => he s)

@[simp] theorem eval_mk (s : Cocone F) (x : Admitted F) :
    eval s (Quotient.mk _ x) = x.val.eval s := rfl

/-- The family of cocone evaluations jointly distinguishes quotient cells. -/
theorem ext {x y : Cell F} (he : ∀ s : Cocone F, eval s x = eval s y) : x = y := by
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y => exact Quotient.sound he

end Cell
end Thomason.Construction.StrictOmegaCategory.ColimitConstruction

end

section

/-! # Faces and matching-boundary compositions on the small colimit carrier -/

namespace Thomason.Construction.StrictOmegaCategory.ColimitConstruction

open CategoryTheory CategoryTheory.Limits

variable {J : Type} [Category.{0} J] {F : J ⥤ StrictOmegaCategory.{0}}

namespace Cell

/-- A representative is used only to define operations; all evaluations
below show that the resulting quotient cells are independent of it. -/
noncomputable def representative (x : Cell F) : Admitted F := Quotient.out x

theorem eval_representative (s : Cocone F) (x : Cell F) :
    (representative x).val.eval s = eval s x :=
  congrArg (eval s) (Quotient.out_eq x)

noncomputable def face (a : Bool) (n : ℕ) (x : Cell F) : Cell F :=
  Quotient.mk _ ⟨.face a n (representative x).val, .face a n (representative x).property⟩

@[simp] theorem eval_face (s : Cocone F) (a : Bool) (n : ℕ) (x : Cell F) :
    eval s (face a n x) = s.pt.face a n (eval s x) := by
  change s.pt.face a n ((representative x).val.eval s) = _
  rw [eval_representative]

/-- Matching quotient boundaries match in every testing cocone. -/
theorem composable_eval (n : ℕ) {x y : Cell F}
    (he : face true n x = face false n y) (s : Cocone F) :
    s.pt.target n (eval s x) = s.pt.source n (eval s y) := by
  have hh := congrArg (eval s) he
  simpa only [eval_face] using hh

/-- Consequently composition of any matching quotient cells is admitted. -/
theorem representative_composable (n : ℕ) {x y : Cell F}
    (he : face true n x = face false n y) (s : Cocone F) :
    s.pt.target n ((representative x).val.eval s) =
      s.pt.source n ((representative y).val.eval s) := by
  rw [eval_representative, eval_representative]
  exact composable_eval n he s

noncomputable def comp (n : ℕ) (x y : Cell F) (he : face true n x = face false n y) : Cell F :=
  Quotient.mk _ ⟨.comp n (representative x).val (representative y).val,
    .comp n (representative x).property (representative y).property
      (representative_composable n he)⟩

/-- Every testing cocone preserves the quotient composition on all cells. -/
theorem eval_comp (s : Cocone F) (n : ℕ) (x y : Cell F)
    (he : face true n x = face false n y) :
    eval s (comp n x y he) = s.pt.comp n (eval s x) (eval s y) (composable_eval n he s) := by
  change Term.eval s (.comp n (representative x).val (representative y).val) = _
  rw [Term.eval_comp s n _ _ (representative_composable n he s)]
  simp only [eval_representative]

end Cell
end Thomason.Construction.StrictOmegaCategory.ColimitConstruction

end

section

/-! # The small colimit carrier satisfies every strict omega-category law -/

namespace Thomason.Construction.StrictOmegaCategory.ColimitConstruction

open CategoryTheory CategoryTheory.Limits

variable {J : Type} [Category.{0} J] (F : J ⥤ StrictOmegaCategory.{0})

/-- Every strict law is detected by the jointly injective cocone evaluations. -/
noncomputable abbrev category : StrictOmegaCategory.{0} where
  Cell := Cell F
  face := Cell.face
  comp := Cell.comp
  globular a b m n x := by
    apply Cell.ext
    intro s
    simpa only [Cell.eval_face, apply_ite] using s.pt.globular a b m n (Cell.eval s x)
  source_comp n x y he := by
    apply Cell.ext
    intro s
    simpa only [Cell.eval_face, Cell.eval_comp] using
      s.pt.source_comp n (Cell.eval s x) (Cell.eval s y) (Cell.composable_eval n he s)
  target_comp n x y he := by
    apply Cell.ext
    intro s
    simpa only [Cell.eval_face, Cell.eval_comp] using
      s.pt.target_comp n (Cell.eval s x) (Cell.eval s y) (Cell.composable_eval n he s)
  face_comp a m n hnm x y he he' := by
    apply Cell.ext
    intro s
    simp only [Cell.eval_face, Cell.eval_comp]
    apply s.pt.face_comp
    exact hnm
  left_unit n x he := by
    apply Cell.ext
    intro s
    simp only [Cell.eval_face, Cell.eval_comp]
    apply s.pt.left_unit
  right_unit n x he := by
    apply Cell.ext
    intro s
    simp only [Cell.eval_face, Cell.eval_comp]
    apply s.pt.right_unit
  assoc n x y z hxy hyz hl hr := by
    apply Cell.ext
    intro s
    simp only [Cell.eval_comp]
    apply s.pt.assoc
  interchange m n hmn a b c d hab hcd hac hbd hl hr := by
    apply Cell.ext
    intro s
    simp only [Cell.eval_comp]
    apply s.pt.interchange
    exact hmn
  finite_dimension x := by
    obtain ⟨n, hn⟩ := Good.uniformDimension F (Cell.representative x).property
    refine ⟨n, ?_, ?_⟩
    · apply Cell.ext
      intro s
      rw [Cell.eval_face]
      have hb := hn s
      rw [Cell.eval_representative] at hb
      exact hb.1
    · apply Cell.ext
      intro s
      rw [Cell.eval_face]
      have hb := hn s
      rw [Cell.eval_representative] at hb
      exact hb.2

/-- Every model evaluation is an actual strict functor. -/
noncomputable def evaluation (s : Cocone F) : category F ⟶ s.pt where
  toFun := Cell.eval s
  map_face := Cell.eval_face s
  map_comp n x y he _he' := Cell.eval_comp s n x y he

end Thomason.Construction.StrictOmegaCategory.ColimitConstruction

end

section

/-! # The canonical cocone of the formal-cell colimit -/

namespace Thomason.Construction.StrictOmegaCategory.ColimitConstruction

open CategoryTheory CategoryTheory.Limits

variable {J : Type} [Category.{0} J] (F : J ⥤ StrictOmegaCategory.{0})

/-- The original diagram cells as quotient cells. -/
def generator (j : J) (x : F.obj j) : Cell F :=
  Quotient.mk _ ⟨.gen j x, .gen j x⟩

@[simp] theorem eval_generator (s : Cocone F) (j : J) (x : F.obj j) :
    Cell.eval s (generator F j x) = (s.ι.app j).toFun x := rfl

/-- Each original diagram object maps by an actual strict functor. -/
noncomputable def leg (j : J) : F.obj j ⟶ category F where
  toFun := generator F j
  map_face a n x := by
    apply Cell.ext
    intro s
    change Cell.eval s (generator F j ((F.obj j).face a n x)) =
      Cell.eval s (Cell.face a n (generator F j x))
    simp only [eval_generator, Cell.eval_face]
    exact (s.ι.app j).map_face a n x
  map_comp n x y he he' := by
    apply Cell.ext
    intro s
    have hq : Cell.face true n (generator F j x) = Cell.face false n (generator F j y) := he'
    exact ((s.ι.app j).map_comp n x y he (Cell.composable_eval n hq s)).trans
      (Cell.eval_comp s n (generator F j x) (generator F j y) hq).symm

/-- All the original diagram relations hold in the quotient. -/
noncomputable def cocone : Cocone F where
  pt := category F
  ι :=
    { app := leg F
      naturality := by
        intro i j f
        apply Hom.ext
        funext x
        apply Cell.ext
        intro s
        exact congrArg (fun k : F.obj i ⟶ s.pt => k.toFun x) (s.ι.naturality f) }

/-- Evaluation extends the prescribed cocone on every original diagram object. -/
theorem evaluation_fac (s : Cocone F) (j : J) :
    leg F j ≫ evaluation F s = s.ι.app j := by
  apply Hom.ext
  rfl

end Thomason.Construction.StrictOmegaCategory.ColimitConstruction

end

section

/-! # The formal-cell cocone has the universal property of a colimit -/

namespace Thomason.Construction.StrictOmegaCategory.ColimitConstruction

open CategoryTheory CategoryTheory.Limits

variable {J : Type} [Category.{0} J] {F : J ⥤ StrictOmegaCategory.{0}}

namespace Cell

/-- A face expression represents the face of the represented cell. -/
theorem mk_face (a : Bool) (n : ℕ) (x : Admitted F) :
    Quotient.mk _ (⟨.face a n x.val, .face a n x.property⟩ : Admitted F) =
      face a n (Quotient.mk _ x) := by
  apply ext
  intro s
  simp only [eval_mk, Term.eval_face, eval_face]

/-- Every admitted composition has matching boundaries in the quotient. -/
theorem mk_match (n : ℕ) (x y : Admitted F)
    (he : ∀ s : Cocone F, s.pt.target n (x.val.eval s) = s.pt.source n (y.val.eval s)) :
    face true n (Quotient.mk _ x) = face false n (Quotient.mk _ y) := by
  apply ext
  intro s
  simpa only [eval_face, eval_mk] using he s

/-- A composition expression represents exactly the quotient composition. -/
theorem mk_comp (n : ℕ) (x y : Admitted F)
    (he : ∀ s : Cocone F, s.pt.target n (x.val.eval s) = s.pt.source n (y.val.eval s))
    (hq : face true n (Quotient.mk _ x) = face false n (Quotient.mk _ y)) :
    Quotient.mk _ (⟨.comp n x.val y.val, .comp n x.property y.property he⟩ : Admitted F) =
      comp n (Quotient.mk _ x) (Quotient.mk _ y) hq := by
  apply ext
  intro s
  simp only [eval_mk, eval_comp]
  exact Term.eval_comp s n x.val y.val (he s)

end Cell

variable (F)

/-- Any strict map agreeing on the diagram generators agrees on all finite
admitted cell expressions. -/
theorem map_term (s : Cocone F) (m : category F ⟶ s.pt)
    (hm : ∀ j, leg F j ≫ m = s.ι.app j) {t : Term F} (ht : Good F t) :
    m.toFun (Quotient.mk _ (⟨t, ht⟩ : Admitted F)) = t.eval s := by
  induction ht with
  | gen j x => exact congrArg (fun k : F.obj j ⟶ s.pt => k.toFun x) (hm j)
  | @face a n x hx ih =>
    rw [Cell.mk_face a n (⟨x, hx⟩ : Admitted F), m.map_face, ih]
    rfl
  | @comp n x y hx hy he ihx ihy =>
    let qx : Cell F := Quotient.mk _ (⟨x, hx⟩ : Admitted F)
    let qy : Cell F := Quotient.mk _ (⟨y, hy⟩ : Admitted F)
    have hq : Cell.face true n qx = Cell.face false n qy := Cell.mk_match n _ _ he
    have hm' : s.pt.target n (m.toFun qx) = s.pt.source n (m.toFun qy) := by
      exact (m.map_face true n qx).symm.trans
        ((congrArg m.toFun hq).trans (m.map_face false n qy))
    rw [Cell.mk_comp n _ _ he hq, m.map_comp n qx qy hq hm']
    change s.pt.comp n (m.toFun qx) (m.toFun qy) hm' = _
    dsimp only [qx, qy] at ihx ihy ⊢
    simp only [ihx, ihy, Term.eval_comp s n x y (he s)]

/-- The original generator legs are jointly epimorphic among strict maps. -/
theorem hom_ext {D : StrictOmegaCategory.{0}} (f g : category F ⟶ D)
    (he : ∀ j, leg F j ≫ f = leg F j ≫ g) : f = g := by
  let s : Cocone F :=
    { pt := D
      ι := (cocone F).ι ≫ (Functor.const J).map g }
  apply Hom.ext
  funext x
  induction x using Quotient.inductionOn with
  | h x =>
    exact (map_term F s f he x.property).trans
      (map_term F s g (fun _ => rfl) x.property).symm

/-- The small semantic quotient is the colimit of the original diagram. -/
noncomputable def isColimit : IsColimit (cocone F) where
  desc := evaluation F
  fac := evaluation_fac F
  uniq s m hm := hom_ext F m (evaluation F s) (fun j => (hm j).trans (evaluation_fac F s j).symm)

end Thomason.Construction.StrictOmegaCategory.ColimitConstruction

end

section

/-! # Nonempty iterated strict composites

The relation retains every actual matching equation. It is shared by the
positive-table uniqueness argument and the generated-expression argument.
-/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory

universe u v

inductive CompositeList (C : StrictOmegaCategory.{u}) (r : ℕ) : List C → C → Prop
  | singleton (x : C) : CompositeList C r [x] x
  | cons (x : C) {xs : List C} {y : C} (hy : CompositeList C r xs y)
      (hxy : C.target r x = C.source r y) :
      CompositeList C r (x :: xs) (C.comp r x y hxy)

namespace CompositeList

variable {C : StrictOmegaCategory.{u}} {D : StrictOmegaCategory.{v}} {r : ℕ}

theorem nonempty {xs : List C} {x : C} (h : CompositeList C r xs x) : xs ≠ [] := by
  cases h <;> simp

/-- Strict functors carry every matching iterated composite to the
corresponding iterated composite of its images. -/
theorem map (F : Hom C D) {xs : List C} {x : C} (h : CompositeList C r xs x) :
    CompositeList D r (xs.map F.toFun) (F.toFun x) := by
  induction h with
  | singleton x => exact .singleton (F.toFun x)
  | @cons x xs y hy hxy ih =>
    have hf : D.target r (F.toFun x) = D.source r (F.toFun y) :=
      (F.map_face true r x).symm.trans
        ((congrArg F.toFun hxy).trans (F.map_face false r y))
    have hc := CompositeList.cons (F.toFun x) ih hf
    simpa only [List.map_cons, F.map_comp r x y hxy hf] using hc

/-- Concatenating two matching strings gives their binary strict composite. -/
theorem append {xs ys : List C} {x y : C}
    (hx : CompositeList C r xs x) (hy : CompositeList C r ys y)
    (hxy : C.target r x = C.source r y) :
    CompositeList C r (xs ++ ys) (C.comp r x y hxy) := by
  induction hx with
  | singleton x => exact .cons x hy hxy
  | @cons z zs x hz hzx ih =>
    have hxy' : C.target r x = C.source r y :=
      (C.target_comp r z x hzx).symm.trans hxy
    have hzxy : C.target r z = C.source r (C.comp r x y hxy') :=
      hzx.trans (C.source_comp r x y hxy').symm
    have hc := CompositeList.cons z (ih hxy') hzxy
    simpa only [List.cons_append, C.assoc r z x y hzx hxy' hxy hzxy] using hc

/-- Every cut with two nonempty sides is a genuine binary factorization. -/
theorem split {xs ys : List C} {z : C}
    (h : CompositeList C r (xs ++ ys) z) (hxs : xs ≠ []) (hys : ys ≠ []) :
    ∃ (x y : C) (hxy : C.target r x = C.source r y),
      CompositeList C r xs x ∧ CompositeList C r ys y ∧ C.comp r x y hxy = z := by
  induction xs generalizing z with
  | nil => exact (hxs rfl).elim
  | cons a xs ih =>
    cases xs with
    | nil =>
      cases h with
      | singleton a => exact (hys rfl).elim
      | @cons a ys y hy hay => exact ⟨a, y, hay, .singleton a, hy, rfl⟩
    | cons b bs =>
      cases h with
      | @cons a rest z hz haz =>
        obtain ⟨x, y, hxy, hx, hy, he⟩ := ih hz (by simp)
        have hax : C.target r a = C.source r x := by
          exact haz.trans ((congrArg (C.source r) he).symm.trans (C.source_comp r x y hxy))
        have hay : C.target r (C.comp r a x hax) = C.source r y :=
          (C.target_comp r a x hax).trans hxy
        refine ⟨C.comp r a x hax, y, hay, .cons a hx hax, hy, ?_⟩
        have har : C.target r a = C.source r (C.comp r x y hxy) :=
          hax.trans (C.source_comp r x y hxy).symm
        exact (C.assoc r a x y hax hxy hay har).trans
          (by subst z; rfl)

end CompositeList
end Thomason.Construction.StrictOmegaCategory

end

section

/-! # Replacing neighbouring factors in an actual strict composite

The replacement retains the total cell and every remaining factor. This
is the context operation needed to sort an atom-labelled factorization.
-/

namespace Thomason.Construction.StrictOmegaCategory.CompositeList

variable {C : StrictOmegaCategory.{0}} {r : ℕ}

theorem total_unique {xs : List C} {x y : C}
    (hx : CompositeList C r xs x) (hy : CompositeList C r xs y) : x = y := by
  induction hx generalizing y with
  | singleton x =>
    cases hy with
    | singleton => rfl
    | @cons x xs y hy hxy => exact (hy.nonempty rfl).elim
  | @cons x xs z hz hxz ih =>
    cases hy with
    | singleton => exact (hz.nonempty rfl).elim
    | @cons x xs w hw hxw =>
      have he := ih hw
      subst w
      rfl

theorem pair (a b : C) (hab : C.target r a = C.source r b) :
    CompositeList C r [a,b] (C.comp r a b hab) := .cons a (.singleton b) hab

theorem replace_first_pair (a b a' b' : C) (as : List C) (x : C)
    (h : CompositeList C r (a :: b :: as) x)
    (hab : C.target r a = C.source r b) (hab' : C.target r a' = C.source r b')
    (he : C.comp r a' b' hab' = C.comp r a b hab) :
    CompositeList C r (a' :: b' :: as) x := by
  cases h with
  | @cons a bs y hy hay =>
    cases hy with
    | singleton b =>
      exact he ▸ pair a' b' hab'
    | @cons b as z hz hbz =>
      have hold : C.target r (C.comp r a b hab) = C.source r z :=
        (C.target_comp r a b hab).trans hbz
      have hnew : C.target r (C.comp r a' b' hab') = C.source r z :=
        (congrArg (C.target r) he).trans hold
      have hl := (pair a' b' hab').append hz hnew
      have hassoc := C.assoc r a b z hab hbz hold hay
      have htotal : C.comp r (C.comp r a' b' hab') z hnew =
          C.comp r a (C.comp r b z hbz) hay := by
        calc
          _ = C.comp r (C.comp r a b hab) z hold := by congr 1
          _ = _ := hassoc
      exact htotal ▸ hl

end Thomason.Construction.StrictOmegaCategory.CompositeList

end

end OAI
