import OAI.CategoryTheory.Thomason.Presentations
import OAI.CategoryTheory.Thomason.Simplicial.CanonicalExtensionCartesian
import OAI.CategoryTheory.Thomason.Strict.StrictCompositeListReplacement
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Homotopy.HomotopyGroup

namespace OAI

section

/-! # Dimension-bounded cells for intelligent truncation

The cells of dimension at most n form a strict n-category. This supplies
the representatives on which the intelligent-truncation congruence acts.
-/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory

variable (C : StrictOmegaCategory.{0})

/-- Lower boundaries of a composite are the corresponding boundaries of
its first factor, by the source law and globularity. -/
theorem lower_face_comp (a : Bool) {k m : ℕ} (hkm : k < m) (x y : C)
    (h : C.target m x = C.source m y) :
    C.face a k (C.comp m x y h) = C.face a k x := by
  have he := congrArg (C.face a k) (C.source_comp m x y h)
  simpa only [C.globular, hkm, ite_true] using he

theorem lower_faces_equal (a : Bool) {k m : ℕ} (hkm : k < m) (x y : C)
    (h : C.target m x = C.source m y) : C.face a k x = C.face a k y := by
  have he := congrArg (C.face a k) h
  simpa only [source, target, C.globular, hkm, ite_true] using he

/-- Boundaries at or below the composition level use the exterior factors. -/
theorem face_comp_le (a : Bool) {k m : ℕ} (hkm : k ≤ m) (x y : C)
    (h : C.target m x = C.source m y) :
    C.face a k (C.comp m x y h) = if a then C.face true k y else C.face false k x := by
  by_cases he : k = m
  · subst m
    cases a
    · exact C.source_comp k x y h
    · exact C.target_comp k x y h
  · have hklt : k < m := by omega
    rw [C.lower_face_comp a hklt x y h]
    cases a
    · rfl
    · exact C.lower_faces_equal true hklt x y h

theorem dimensionLE_face {n : ℕ} {x : C} (hx : C.DimensionLE n x) (a : Bool) (m : ℕ) :
    C.DimensionLE n (C.face a m x) := by
  change C.face false n (C.face a m x) = C.face a m x ∧
    C.face true n (C.face a m x) = C.face a m x
  by_cases hnm : n < m
  · have hm := C.dimensionLE_mono (Nat.le_of_lt hnm) hx
    have he : C.face a m x = x := by
      cases a
      · exact hm.1
      · exact hm.2
    simp only [he, hx.1, hx.2, and_self]
  · simp only [C.globular, hnm, ite_false, and_self]

/-- Composing above the dimension of both cells is composition of identities. -/
theorem comp_of_dimensionLE {n m : ℕ} (hnm : n ≤ m) {x y : C}
    (hx : C.DimensionLE n x) (h : C.target m x = C.source m y) : C.comp m x y h = y := by
  have hs : C.face false m x = x := (C.dimensionLE_mono hnm hx).1
  have ht : C.face true m x = x := (C.dimensionLE_mono hnm hx).2
  have he : C.face false m y = x := h.symm.trans ht
  have hu := C.left_unit m y (C.face_face_same true false m y)
  simpa only [he] using hu

theorem dimensionLE_comp_all {n m : ℕ} {x y : C}
    (hx : C.DimensionLE n x) (hy : C.DimensionLE n y)
    (h : C.target m x = C.source m y) : C.DimensionLE n (C.comp m x y h) := by
  by_cases hmn : m < n
  · exact C.dimensionLE_comp hmn hx hy h
  · rw [C.comp_of_dimensionLE (by omega) hx h]
    exact hy

/-- The actual subcategory of cells of dimension at most n. -/
def bounded (n : ℕ) : StrictOmegaCategory.{0} where
  Cell := {x : C // C.DimensionLE n x}
  face a m x := ⟨C.face a m x.val, C.dimensionLE_face x.property a m⟩
  globular a b k m x := by
    apply Subtype.ext
    exact (C.globular a b k m x.val).trans (by split_ifs <;> rfl)
  comp m x y h := ⟨C.comp m x.val y.val (congrArg Subtype.val h),
    C.dimensionLE_comp_all x.property y.property _⟩
  source_comp m x y h := Subtype.ext (C.source_comp m x.val y.val _)
  target_comp m x y h := Subtype.ext (C.target_comp m x.val y.val _)
  face_comp a k m hmk x y h h' := Subtype.ext (C.face_comp a k m hmk x.val y.val _ _)
  left_unit m x h := Subtype.ext (C.left_unit m x.val _)
  right_unit m x h := Subtype.ext (C.right_unit m x.val _)
  assoc m x y z hxy hyz hl hr := Subtype.ext (C.assoc m x.val y.val z.val _ _ _ _)
  interchange k m hkm a b c d hab hcd hac hbd hl hr :=
    Subtype.ext (C.interchange k m hkm a.val b.val c.val d.val _ _ _ _ _ _)
  finite_dimension x := ⟨n, Subtype.ext x.property.1, Subtype.ext x.property.2⟩

theorem bounded_isTruncated (n : ℕ) : (C.bounded n).IsTruncated n :=
  fun x => ⟨Subtype.ext x.property.1, Subtype.ext x.property.2⟩

def boundedInclusion (n : ℕ) : C.bounded n ⟶ C where
  toFun := Subtype.val
  map_face _ _ _ := rfl
  map_comp _ _ _ _ _ := rfl

end Thomason.Construction.StrictOmegaCategory

end

section

/-!
# The semantic weak equivalences used in the Thomason construction

A topological map is a weak homotopy equivalence when it induces bijections
on path components and on every positive-dimensional based homotopy group.
Here the maps on homotopy groups are constructed on the actual generalized
loops from Mathlib. The simplicial weak equivalences are then defined by
geometric realization, rather than an unspecified morphism property.

When applying subdivision transport, the two-out-of-three assertion for
these actual weak equivalences is kept as the published Kan–Quillen input
(Goerss–Jardine, I.11.3–I.11.4 and Corollary II.8.6), as are last vertex and extension (III.4.6).
-/

namespace Thomason.Construction

open CategoryTheory

universe u

namespace HomotopyMaps

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

noncomputable def loopMap (f : C(X, Y)) {x : X} {N : Type*} (p : GenLoop N X x) : GenLoop N Y (f x) :=
  Thomason.WeakHomotopy.loopMap N f x p

theorem loopMap_homotopic (f : C(X, Y)) {x : X} {N : Type*}
    {p q : GenLoop N X x} (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (loopMap f p) (loopMap f q) :=
  h.comp_continuousMap f

noncomputable def groupMap (f : C(X, Y)) (n : ℕ) (x : X) :
    HomotopyGroup.Pi n X x → HomotopyGroup.Pi n Y (f x) :=
  Thomason.WeakHomotopy.groupMap (Fin n) f x

noncomputable def componentsMap (f : C(X, Y)) : ZerothHomotopy X → ZerothHomotopy Y :=
  Thomason.WeakHomotopy.componentsMap f

@[simp]
theorem componentsMap_mk (f : C(X, Y)) (x : X) :
    componentsMap f (.mk x) = .mk (f x) := rfl

@[simp]
theorem componentsMap_id : componentsMap (ContinuousMap.id X) = id := by
  funext x
  induction x using ZerothHomotopy.rec with
  | mk x => rfl

theorem componentsMap_comp (f : C(X, Y)) (g : C(Y, Z)) :
    componentsMap (g.comp f) = componentsMap g ∘ componentsMap f := by
  funext x
  induction x using ZerothHomotopy.rec with
  | mk x => rfl

@[simp]
theorem groupMap_id (n : ℕ) (x : X) : groupMap (ContinuousMap.id X) n x = id := by
  funext p
  induction p using Quotient.inductionOn with
  | h p =>
    apply congrArg (Quotient.mk _)
    apply GenLoop.ext
    intro t
    rfl

theorem groupMap_comp (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) (x : X) :
    groupMap (g.comp f) n x = groupMap g n (f x) ∘ groupMap f n x := by
  funext p
  induction p using Quotient.inductionOn with
  | h p =>
    apply congrArg (Quotient.mk _)
    apply GenLoop.ext
    intro t
    rfl

end HomotopyMaps

/-- The actual weak homotopy equivalences, using path components and all
positive-dimensional homotopy groups of the source at all basepoints. -/
def IsWeakHomotopyEquivalence {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : Prop :=
  Function.Bijective (HomotopyMaps.componentsMap f) ∧
  ∀ (n : ℕ) (x : X), Function.Bijective (HomotopyMaps.groupMap f (n + 1) x)

/-- The component and homotopy-group criterion is the common weak-homotopy test. -/
theorem isWeakHomotopyEquivalence_iff {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    IsWeakHomotopyEquivalence f ↔ Thomason.WeakHomotopy.Equivalence f := Iff.rfl

namespace IsWeakHomotopyEquivalence

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

theorem id : IsWeakHomotopyEquivalence (ContinuousMap.id X) := by
  constructor
  · simpa using Function.bijective_id (α := ZerothHomotopy X)
  · intro n x
    simpa using Function.bijective_id (α := HomotopyGroup.Pi (n + 1) X x)

theorem comp {f : C(X, Y)} {g : C(Y, Z)}
    (hf : IsWeakHomotopyEquivalence f) (hg : IsWeakHomotopyEquivalence g) :
    IsWeakHomotopyEquivalence (g.comp f) := by
  constructor
  · rw [HomotopyMaps.componentsMap_comp]
    exact hg.1.comp hf.1
  · intro n x
    rw [HomotopyMaps.groupMap_comp]
    exact (hg.2 n (f x)).comp (hf.2 n x)

end IsWeakHomotopyEquivalence

def topologicalWeakEquivalences : MorphismProperty TopCat.{u} :=
  fun _ _ f => IsWeakHomotopyEquivalence f.hom

/-- Kan–Quillen weak equivalences as weak homotopy equivalences of geometric
realizations. No model structure is presupposed by this definition. -/
def realizationWeakEquivalences : MorphismProperty SSet.{u} :=
  topologicalWeakEquivalences.inverseImage SSet.toTop

/-- Both simplicial classes use the same weak-homotopy test on realization. -/
theorem realizationWeakEquivalences_eq :
    realizationWeakEquivalences.{u} = Thomason.simplicialWeakEquivalences := rfl

instance : topologicalWeakEquivalences.{u}.ContainsIdentities where
  id_mem _ := IsWeakHomotopyEquivalence.id

instance : topologicalWeakEquivalences.{u}.IsStableUnderComposition where
  comp_mem _ _ hf hg := hf.comp hg

instance : realizationWeakEquivalences.{u}.ContainsIdentities :=
  inferInstanceAs (topologicalWeakEquivalences.{u}.inverseImage SSet.toTop).ContainsIdentities
instance : realizationWeakEquivalences.{u}.IsStableUnderComposition :=
  inferInstanceAs
    (topologicalWeakEquivalences.{u}.inverseImage SSet.toTop).IsStableUnderComposition

/-- Extension twice preserves and reflects realization weak equivalences
under the classical Kan–Quillen hypotheses. -/
theorem realization_ex_twice_iff
    [realizationWeakEquivalences.{u}.HasTwoOutOfThreeProperty]
    (hj : ∀ X, realizationWeakEquivalences.{u} (canonicalExtension.app X))
    {X Y : SSet.{u}} (f : X ⟶ Y) :
    realizationWeakEquivalences.{u} ((SSet.ex ⋙ SSet.ex).map f) ↔
      realizationWeakEquivalences.{u} f :=
  ex_twice_map_iff realizationWeakEquivalences.{u} canonicalExtension hj f

end Thomason.Construction

end

section

/-! # Homeomorphisms and isomorphisms are actual realization weak equivalences

The maps on generalized loops and their homotopy quotients are explicit.
No Kan–Quillen factorization or two-out-of-three input is used here.
-/

namespace Thomason.Construction

open CategoryTheory

universe u

namespace HomotopyMaps

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- A homeomorphism gives an actual equivalence on based generalized loops. -/
noncomputable def loopHomeomorphEquiv (e : X ≃ₜ Y) (x : X) (N : Type*) :
    GenLoop N X x ≃ GenLoop N Y (e x) where
  toFun := loopMap (e : C(X, Y))
  invFun q := ⟨(e.symm : C(Y, X)).comp q.val, fun t ht =>
    (congrArg e.symm (q.property t ht)).trans (e.symm_apply_apply x)⟩
  left_inv p := by
    apply GenLoop.ext
    intro t
    exact e.symm_apply_apply (p t)
  right_inv q := by
    apply GenLoop.ext
    intro t
    exact e.apply_symm_apply (q t)

/-- The loop equivalence preserves and reflects homotopy relative to the boundary. -/
theorem loopHomeomorphEquiv_homotopic (e : X ≃ₜ Y) (x : X) {N : Type*}
    (p q : GenLoop N X x) :
    GenLoop.Homotopic p q ↔
      GenLoop.Homotopic (loopHomeomorphEquiv e x N p) (loopHomeomorphEquiv e x N q) := by
  constructor
  · exact fun hp => hp.comp_continuousMap (e : C(X, Y))
  · intro hp
    have hr := hp.comp_continuousMap (e.symm : C(Y, X))
    have hloop (a : GenLoop N X x) :
        (e.symm : C(Y, X)).comp ((loopHomeomorphEquiv e x N a).val) = a.val := by
      apply ContinuousMap.ext
      intro t
      exact e.symm_apply_apply (a t)
    change ((e.symm : C(Y, X)).comp ((loopHomeomorphEquiv e x N p).val)).HomotopicRel
      ((e.symm : C(Y, X)).comp ((loopHomeomorphEquiv e x N q).val)) (Cube.boundary N) at hr
    rw [hloop p, hloop q] at hr
    exact hr

/-- The induced map on actual homotopy groups is bijective. -/
theorem groupMap_homeomorph_bijective (e : X ≃ₜ Y) (n : ℕ) (x : X) :
    Function.Bijective (groupMap (e : C(X, Y)) n x) :=
  (Quotient.congr (loopHomeomorphEquiv e x (Fin n))
    (loopHomeomorphEquiv_homotopic e x)).bijective

/-- The induced map on path components is bijective as well. -/
theorem componentsMap_homeomorph_bijective (e : X ≃ₜ Y) :
    Function.Bijective (componentsMap (e : C(X, Y))) := by
  have hl : Function.LeftInverse (componentsMap (e.symm : C(Y, X)))
      (componentsMap (e : C(X, Y))) := by
    intro a
    induction a using ZerothHomotopy.rec with
    | mk a => exact congrArg ZerothHomotopy.mk (e.symm_apply_apply a)
  have hr : Function.RightInverse (componentsMap (e.symm : C(Y, X)))
      (componentsMap (e : C(X, Y))) := by
    intro a
    induction a using ZerothHomotopy.rec with
    | mk a => exact congrArg ZerothHomotopy.mk (e.apply_symm_apply a)
  exact ⟨hl.injective, hr.surjective⟩

end HomotopyMaps

/-- Every homeomorphism satisfies the actual component-and-homotopy-group definition. -/
theorem homeomorph_isWeakHomotopyEquivalence {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    IsWeakHomotopyEquivalence (e : C(X, Y)) :=
  ⟨HomotopyMaps.componentsMap_homeomorph_bijective e,
    fun n x => HomotopyMaps.groupMap_homeomorph_bijective e (n+1) x⟩

/-- Topological isomorphisms are weak before any model structure is supplied. -/
theorem topologicalWeakEquivalences_of_isIso {X Y : TopCat.{u}}
    (f : X ⟶ Y) [IsIso f] : topologicalWeakEquivalences f :=
  homeomorph_isWeakHomotopyEquivalence (TopCat.homeoOfIso (asIso f))

instance : topologicalWeakEquivalences.{u}.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) => topologicalWeakEquivalences_of_isIso f)

/-- Geometric realization therefore respects isomorphic simplicial maps unconditionally. -/
instance : realizationWeakEquivalences.{u}.RespectsIso :=
  inferInstanceAs (topologicalWeakEquivalences.{u}.inverseImage SSet.toTop).RespectsIso

end Thomason.Construction

end

section

/-! # Based homotopy groups as actual functors

The under category of the one-point topological space keeps track of
basepoints and their equalities. The resulting functor uses the same
homotopy quotients as the realization weak-equivalence definition.
-/

namespace Thomason.Construction

open CategoryTheory

universe u

namespace HomotopyMaps

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Postcomposition with an explicitly preserved basepoint. -/
def basedLoopMap (f : C(X, Y)) {x : X} {y : Y} (e : f x = y)
    {N : Type*} (p : GenLoop N X x) : GenLoop N Y y :=
  ⟨f.comp p.val, fun t ht => (congrArg f (p.property t ht)).trans e⟩

/-- The corresponding map on the actual based homotopy quotient. -/
def basedGroupMap (f : C(X, Y)) {x : X} {y : Y} (e : f x = y) (n : ℕ) :
    HomotopyGroup.Pi n X x → HomotopyGroup.Pi n Y y :=
  Quotient.map (basedLoopMap f e) (fun _ _ hp => hp.comp_continuousMap f)

@[simp]
theorem basedGroupMap_rfl (f : C(X, Y)) (x : X) (n : ℕ) :
    basedGroupMap f (x := x) rfl n = groupMap f n x := rfl

/-- Transporting the target basepoint does not change bijectivity. -/
theorem basedGroupMap_bijective_iff (f : C(X, Y)) {x : X} {y : Y}
    (e : f x = y) (n : ℕ) :
    Function.Bijective (basedGroupMap f e n) ↔ Function.Bijective (groupMap f n x) := by
  subst y
  rfl

end HomotopyMaps

namespace PointedHomotopyGroups

abbrev Pointed := Under (TopCat.of PUnit.{u+1})

def point (X : Pointed.{u}) : X.right := X.hom.hom PUnit.unit

theorem map_point {X Y : Pointed.{u}} (f : X ⟶ Y) : f.right.hom (point X) = point Y :=
  congrArg (fun k => k.hom PUnit.unit) (Under.w f)

/-- The actual homotopy group quotient, functorially in based spaces. -/
def homotopyGroupFunctor (n : ℕ) : Pointed.{u} ⥤ Type u where
  obj X := HomotopyGroup.Pi n X.right (point X)
  map f := ↾(HomotopyMaps.basedGroupMap f.right.hom (map_point f) n)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro p
    induction p using Quotient.inductionOn with
    | h p =>
      apply congrArg (Quotient.mk _)
      apply GenLoop.ext
      intro t
      rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro p
    induction p using Quotient.inductionOn with
    | h p =>
      apply congrArg (Quotient.mk _)
      apply GenLoop.ext
      intro t
      rfl

/-- A space with a chosen actual point. -/
def pointed (X : TopCat.{u}) (x : X) : Pointed.{u} :=
  Under.mk (TopCat.ofHom (ContinuousMap.const PUnit x))

/-- A continuous map with an equality of the chosen basepoints. -/
def pointedMap {X Y : TopCat.{u}} (f : X ⟶ Y) {x : X} {y : Y} (e : f.hom x = y) :
    pointed X x ⟶ pointed Y y :=
  Under.homMk f (by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro t
    exact e)

/-- The functor recovers exactly the map used to define weak equivalences. -/
theorem map_bijective_iff {X Y : TopCat.{u}} (f : X ⟶ Y) {x : X} {y : Y}
    (e : f.hom x = y) (n : ℕ) :
    Function.Bijective ((homotopyGroupFunctor n).map (pointedMap f e)) ↔
      Function.Bijective (HomotopyMaps.groupMap f.hom n x) :=
  HomotopyMaps.basedGroupMap_bijective_iff f.hom e n

/-- Path components form a functor on unbased spaces. -/
noncomputable def componentsFunctor : TopCat.{u} ⥤ Type u where
  obj X := ZerothHomotopy X
  map f := ↾(HomotopyMaps.componentsMap f.hom)
  map_id X := by
    apply ConcreteCategory.hom_ext
    exact congrFun HomotopyMaps.componentsMap_id
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    exact congrFun (HomotopyMaps.componentsMap_comp f.hom g.hom)

end PointedHomotopyGroups
end Thomason.Construction

end

section

/-! # Natural basepoint transport in the actual first homotopy group

The generalized-loop definition used by realization weak equivalences is
identified with Mathlib's fundamental group. Path conjugation then gives
natural basepoint transport and invariance of the bijectivity test in degree one.
-/

namespace Thomason.Construction.HomotopyMaps

open CategoryTheory

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual first-homotopy-group map agrees with the fundamental-group map. -/
theorem piOneEquiv_naturality (f : C(X, Y)) (x : X) (q : HomotopyGroup.Pi 1 X x) :
    HomotopyGroup.pi1EquivFundamentalGroup (groupMap f 1 x q) =
      FundamentalGroup.map f x (HomotopyGroup.pi1EquivFundamentalGroup q) := by
  induction q using Quotient.inductionOn with
  | h q => rfl

/-- Transport the actual cubical first homotopy group along a path. -/
noncomputable def piOneTransport {x y : X} (p : Path x y) :
    HomotopyGroup.Pi 1 X x ≃ HomotopyGroup.Pi 1 X y :=
  HomotopyGroup.pi1EquivFundamentalGroup.trans
    ((FundamentalGroup.fundamentalGroupMulEquivOfPath p).toEquiv.trans
      HomotopyGroup.pi1EquivFundamentalGroup.symm)

/-- Fundamental-group conjugation is natural in continuous maps. -/
theorem fundamentalTransport_naturality (f : C(X, Y)) {x y : X} (p : Path x y)
    (q : FundamentalGroup X x) :
    FundamentalGroup.map f y (FundamentalGroup.fundamentalGroupMulEquivOfPath p q) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map f.continuous)
        (FundamentalGroup.map f x q) := by
  let e := (Groupoid.isoEquivHom (FundamentalGroupoid.mk x) (FundamentalGroupoid.mk y)).symm
    (⟦p⟧ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y)
  have he : (FundamentalGroupoid.map f).mapIso e =
      (Groupoid.isoEquivHom (FundamentalGroupoid.mk (f x))
        (FundamentalGroupoid.mk (f y))).symm
          (⟦p.map f.continuous⟧ : FundamentalGroupoid.mk (f x) ⟶ FundamentalGroupoid.mk (f y)) := by
    apply Iso.ext
    rfl
  change (FundamentalGroupoid.map f).map (e.conj q) = _
  rw [Functor.map_conj, he]
  rfl

/-- The first-homotopy-group square commutes with path basepoint transport. -/
theorem piOneTransport_naturality (f : C(X, Y)) {x y : X} (p : Path x y)
    (q : HomotopyGroup.Pi 1 X x) :
    groupMap f 1 y (piOneTransport p q) = piOneTransport (p.map f.continuous) (groupMap f 1 x q) := by
  apply HomotopyGroup.pi1EquivFundamentalGroup.injective
  rw [piOneEquiv_naturality]
  simp only [piOneTransport, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [piOneEquiv_naturality]
  exact fundamentalTransport_naturality f p _

/-- Bijectivity on the actual first homotopy group is independent of a
basepoint within its path component. -/
theorem groupMap_one_bijective_iff (f : C(X, Y)) {x y : X} (p : Path x y) :
    Function.Bijective (groupMap f 1 x) ↔ Function.Bijective (groupMap f 1 y) := by
  have he : groupMap f 1 y ∘ piOneTransport p =
      piOneTransport (p.map f.continuous) ∘ groupMap f 1 x := by
    funext q
    exact piOneTransport_naturality f p q
  rw [← (piOneTransport p).bijective.of_comp_iff (groupMap f 1 y), he,
    (piOneTransport (p.map f.continuous)).bijective.of_comp_iff']

/-- The degree-one part of weak source cancellation holds at every target
basepoint, using component surjectivity and natural path transport. -/
theorem source_cancel_piOne {Z : Type u} [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (hf : IsWeakHomotopyEquivalence f)
    (hfg : IsWeakHomotopyEquivalence (g.comp f)) (y : Y) :
    Function.Bijective (groupMap g 1 y) := by
  obtain ⟨c, hc⟩ := hf.1.2 (ZerothHomotopy.mk y)
  obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective c
  obtain ⟨p⟩ : Joined (f x) y := Quotient.exact hc
  have hb : Function.Bijective (groupMap g 1 (f x)) := by
    apply ((hf.2 0 x).of_comp_iff _).mp
    simpa only [groupMap_comp] using hfg.2 0 x
  exact (groupMap_one_bijective_iff g p).mp hb

end Thomason.Construction.HomotopyMaps

end

section

/-! # Continuous path-space operations for basepoint transport

These are operations on the actual compact-open path spaces. The eventual
higher-dimensional transport uses their continuous homotopies, not only
equalities in the fundamental-group quotient.
-/

namespace Thomason.Construction.PathSpace

open CategoryTheory

universe u

noncomputable section

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Postcomposition is continuous on path spaces. -/
def map (f : C(X, Y)) {x y : X} : C(Path x y, Path (f x) (f y)) where
  toFun p := p.map f.continuous
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun a : Path x y × unitInterval => f (a.1 a.2))
    fun_prop

/-- Concatenation is an actual continuous operation. -/
def concatenate {x y z : X} : C(Path x y × Path y z, Path x z) :=
  ⟨fun p => p.1.trans p.2, Path.continuous_trans⟩

/-- Reverse a path continuously. -/
def reverse {x y : X} : C(Path x y, Path y x) := ⟨Path.symm, Path.continuous_symm⟩

/-- Conjugation by a fixed path, on unquotiented loop spaces. -/
def conjugate {x y : X} (p : Path x y) : C(Path x x, Path y y) where
  toFun q := (p.symm.trans q).trans p
  continuous_toFun := by fun_prop

/-- The continuous conjugation operation is natural in the ambient space. -/
theorem conjugate_naturality (f : C(X, Y)) {x y : X} (p : Path x y) :
    (map f).comp (conjugate p) = (conjugate (p.map f.continuous)).comp (map f) := by
  apply ContinuousMap.ext
  intro q
  change ((p.symm.trans q).trans p).map f.continuous = _
  rw [Path.map_trans, Path.map_trans, ← Path.map_symm]
  rfl

/-- The path-space version of concatenating a fixed homotopy with a variable path. -/
def appendHomotopy {x y z : X} {p q : Path x y} (H : p.Homotopy q) :
    (⟨fun r : Path y z => p.trans r, by fun_prop⟩ : C(Path y z, Path x z)).Homotopy
      ⟨fun r => q.trans r, by fun_prop⟩ where
  toFun tr := (H.eval tr.1).trans tr.2
  continuous_toFun := by
    apply Continuous.path_trans
    · apply Path.continuous_uncurry_iff.mp
      change Continuous (fun a : (unitInterval × Path y z) × unitInterval => H (a.1.1, a.2))
      exact H.continuous.comp (by fun_prop)
    · exact continuous_snd
  map_zero_left r := by rw [Path.Homotopy.eval_zero]; rfl
  map_one_left r := by rw [Path.Homotopy.eval_one]; rfl

/-- The path-space version of concatenating a variable path with a fixed homotopy. -/
def prependHomotopy {x y z : X} {p q : Path y z} (H : p.Homotopy q) :
    (⟨fun r : Path x y => r.trans p, by fun_prop⟩ : C(Path x y, Path x z)).Homotopy
      ⟨fun r => r.trans q, by fun_prop⟩ where
  toFun tr := tr.2.trans (H.eval tr.1)
  continuous_toFun := by
    apply Continuous.path_trans
    · exact continuous_snd
    · apply Path.continuous_uncurry_iff.mp
      change Continuous (fun a : (unitInterval × Path x y) × unitInterval => H (a.1.1, a.2))
      exact H.continuous.comp (by fun_prop)
  map_zero_left r := by rw [Path.Homotopy.eval_zero]; rfl
  map_one_left r := by rw [Path.Homotopy.eval_one]; rfl

end

end Thomason.Construction.PathSpace

end

section

/-! # Continuous reparametrization and association of path-space concatenation -/

namespace Thomason.Construction.PathSpace

open CategoryTheory

universe u

noncomputable section

variable {X : Type u} [TopologicalSpace X]

/-- Reparametrize every path by the same endpoint-preserving interval map. -/
def reparametrize (α : unitInterval → unitInterval) (hα : Continuous α)
    (h₀ : α 0 = 0) (h₁ : α 1 = 1) {x y : X} : C(Path x y, Path x y) where
  toFun p := p.reparam α hα h₀ h₁
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun a : Path x y × unitInterval => a.1 (α a.2))
    fun_prop

/-- Straight-line interpolation is continuous in both the path and its parameter. -/
def reparametrizeHomotopy (α : unitInterval → unitInterval) (hα : Continuous α)
    (h₀ : α 0 = 0) (h₁ : α 1 = 1) {x y : X} :
    (ContinuousMap.id (Path x y)).Homotopy (reparametrize α hα h₀ h₁) where
  toFun tp := (Path.Homotopy.reparam tp.2 α hα h₀ h₁).eval tp.1
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun a : (unitInterval × Path x y) × unitInterval =>
      a.1.2 ⟨(unitInterval.symm a.1.1 : ℝ) * a.2 + a.1.1 * α a.2, _⟩)
    fun_prop
  map_zero_left p := Path.Homotopy.eval_zero _
  map_one_left p := Path.Homotopy.eval_one _

/-- The fixed interval map relating the two associations of three paths. -/
def associatingParameter (t : unitInterval) : unitInterval :=
  ⟨Path.Homotopy.transAssocReparamAux t, Path.Homotopy.transAssocReparamAux_mem_I t⟩

theorem associatingParameter_continuous : Continuous associatingParameter := by
  exact Path.Homotopy.continuous_transAssocReparamAux.subtype_mk _

theorem associatingParameter_zero : associatingParameter 0 = 0 :=
  Subtype.ext Path.Homotopy.transAssocReparamAux_zero

theorem associatingParameter_one : associatingParameter 1 = 1 :=
  Subtype.ext Path.Homotopy.transAssocReparamAux_one

def leftAssociation {a b c d : X} : C(Path a b × Path b c × Path c d, Path a d) where
  toFun p := (p.1.trans p.2.1).trans p.2.2
  continuous_toFun := by fun_prop

def rightAssociation {a b c d : X} : C(Path a b × Path b c × Path c d, Path a d) where
  toFun p := p.1.trans (p.2.1.trans p.2.2)
  continuous_toFun := by fun_prop

/-- Association is a continuous homotopy on the entire space of three paths. -/
def associatingHomotopy {a b c d : X} :
    (leftAssociation (a := a) (b := b) (c := c) (d := d)).Homotopy rightAssociation := by
  have he : (reparametrize associatingParameter associatingParameter_continuous
      associatingParameter_zero associatingParameter_one).comp rightAssociation =
      (leftAssociation (a := a) (b := b) (c := c) (d := d)) := by
    apply ContinuousMap.ext
    intro p
    exact (Path.Homotopy.trans_assoc_reparam p.1 p.2.1 p.2.2).symm
  exact ((reparametrizeHomotopy associatingParameter associatingParameter_continuous
    associatingParameter_zero associatingParameter_one).compContinuousMap rightAssociation).symm.cast he rfl

end

end Thomason.Construction.PathSpace

end

section

/-! # Continuous unit and cancellation homotopies on path spaces -/

namespace Thomason.Construction.PathSpace

universe u

noncomputable section

variable {X : Type u} [TopologicalSpace X]

/-- Append a fixed path on the left. -/
def leftAppend {a b c : X} (p : Path a b) : C(Path b c, Path a c) :=
  ⟨fun q => p.trans q, by fun_prop⟩

/-- Append a fixed path on the right. -/
def rightAppend {a b c : X} (p : Path b c) : C(Path a b, Path a c) :=
  ⟨fun q => q.trans p, by fun_prop⟩

private def unitParameter (t : unitInterval) : unitInterval :=
  ⟨Path.Homotopy.transReflReparamAux t, Path.Homotopy.transReflReparamAux_mem_I t⟩

/-- The right unit law is a homotopy continuous in the entire path. -/
def rightUnitHomotopy (a b : X) :
    (rightAppend (a := a) (Path.refl b)).Homotopy (ContinuousMap.id (Path a b)) := by
  have he : reparametrize unitParameter
      (Path.Homotopy.continuous_transReflReparamAux.subtype_mk _)
      (Subtype.ext Path.Homotopy.transReflReparamAux_zero)
      (Subtype.ext Path.Homotopy.transReflReparamAux_one) =
      rightAppend (a := a) (Path.refl b) := by
    apply ContinuousMap.ext
    intro p
    exact (Path.Homotopy.trans_refl_reparam p).symm
  exact (reparametrizeHomotopy unitParameter
    (Path.Homotopy.continuous_transReflReparamAux.subtype_mk _)
    (Subtype.ext Path.Homotopy.transReflReparamAux_zero)
    (Subtype.ext Path.Homotopy.transReflReparamAux_one)).symm.cast he rfl

/-- The left unit law follows by reversing the continuous right unit homotopy. -/
def leftUnitHomotopy (a b : X) :
    (leftAppend (c := b) (Path.refl a)).Homotopy (ContinuousMap.id (Path a b)) := by
  let H := ((ContinuousMap.Homotopy.refl (reverse (x := b) (y := a))).comp
    ((rightUnitHomotopy b a).compContinuousMap reverse))
  apply H.cast
  · apply ContinuousMap.ext
    intro p
    change (p.symm.trans (Path.refl a)).symm = (Path.refl a).trans p
    simp only [Path.trans_symm, Path.refl_symm, Path.symm_symm]
  · apply ContinuousMap.ext
    exact fun p => Path.symm_symm p

/-- Cancelling a path and its reverse on the left, uniformly in the remaining path. -/
def leftCancellation {a b c : X} (p : Path a b) :
    ((leftAppend (c := c) p.symm).comp (leftAppend p)).Homotopy
      (ContinuousMap.id (Path b c)) := by
  let A := (associatingHomotopy (a := b) (b := a) (c := b) (d := c)).compContinuousMap
    (⟨fun q => (p.symm, p, q), by fun_prop⟩ : C(Path b c, _))
  exact A.symm.trans ((appendHomotopy (Path.Homotopy.reflSymmTrans p).symm).trans
    (leftUnitHomotopy b c))

/-- Cancelling a path and its reverse on the right, uniformly in the preceding path. -/
def rightCancellation {a b c : X} (p : Path b c) :
    ((rightAppend (a := a) p.symm).comp (rightAppend p)).Homotopy
      (ContinuousMap.id (Path a b)) := by
  let A := (associatingHomotopy (a := a) (b := b) (c := c) (d := b)).compContinuousMap
    (⟨fun q => (q, p, p.symm), by fun_prop⟩ : C(Path a b, _))
  exact A.trans ((prependHomotopy (Path.Homotopy.reflTransSymm p).symm).trans
    (rightUnitHomotopy a b))

end

end Thomason.Construction.PathSpace

end

section

/-! # Actual homotopy equivalences induced by concatenating paths

All inverse laws are continuous homotopies on compact-open path spaces.
In particular, path conjugation is a natural homotopy equivalence before
passing to any homotopy-group quotient.
-/

namespace Thomason.Construction.PathSpace

universe u

noncomputable section

variable {X : Type u} [TopologicalSpace X]

/-- Concatenating a fixed path on the left is a homotopy equivalence. -/
def leftAppendEquiv {a b : X} (p : Path a b) (c : X) :
    ContinuousMap.HomotopyEquiv (Path b c) (Path a c) where
  toFun := leftAppend p
  invFun := leftAppend p.symm
  left_inv := ⟨leftCancellation p⟩
  right_inv := by
    have H := leftCancellation (c := c) p.symm
    refine ⟨?_⟩
    simpa only [Path.symm_symm] using H

/-- Concatenating a fixed path on the right is a homotopy equivalence. -/
def rightAppendEquiv (a : X) {b c : X} (p : Path b c) :
    ContinuousMap.HomotopyEquiv (Path a b) (Path a c) where
  toFun := rightAppend p
  invFun := rightAppend p.symm
  left_inv := ⟨rightCancellation p⟩
  right_inv := by
    have H := rightCancellation (a := a) p.symm
    refine ⟨?_⟩
    simpa only [Path.symm_symm] using H

/-- Conjugation gives an actual homotopy equivalence of loop spaces. -/
def conjugateEquiv {a b : X} (p : Path a b) :
    ContinuousMap.HomotopyEquiv (Path a a) (Path b b) :=
  (leftAppendEquiv p.symm a).trans (rightAppendEquiv b p)

@[simp]
theorem conjugateEquiv_toFun {a b : X} (p : Path a b) :
    (conjugateEquiv p).toFun = conjugate p := rfl

/-- The image of the constant loop under conjugation is joined to the
constant loop. This path supplies the needed basepoint comparison. -/
def conjugateConstantPath {a b : X} (p : Path a b) :
    Path (conjugate p (Path.refl a)) (Path.refl b) where
  toFun t := (((Path.Homotopy.transRefl p.symm).hcomp (Path.Homotopy.refl p)).trans
    (Path.Homotopy.reflSymmTrans p).symm).eval t
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact (((Path.Homotopy.transRefl p.symm).hcomp (Path.Homotopy.refl p)).trans
      (Path.Homotopy.reflSymmTrans p).symm).continuous
  source' := Path.Homotopy.eval_zero _
  target' := Path.Homotopy.eval_one _

end

end Thomason.Construction.PathSpace

end

section

/-! # The actual dimension shift from cubes to loops in path spaces

The equivalence and its naturality use the same cubical homotopy quotients
as the definition of realization weak equivalence.
-/

namespace Thomason.Construction.HomotopyMaps

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Curry the first coordinate of a based cube into a based path. -/
def curryLoop {x : X} {n : ℕ} (p : GenLoop (Fin (n+1)) X x) :
    GenLoop (Fin n) (Path x x) (Path.refl x) := by
  refine ⟨⟨fun t => ⟨⟨fun s => p (Fin.cons s t), by fun_prop⟩, ?_, ?_⟩, ?_⟩, ?_⟩
  · exact p.property _ ⟨0, Or.inl rfl⟩
  · exact p.property _ ⟨0, Or.inr rfl⟩
  · apply Path.continuous_uncurry_iff.mp
    change Continuous (fun a : (Fin n → unitInterval) × unitInterval => p (Fin.cons a.2 a.1))
    fun_prop
  · rintro t ⟨i, hi⟩
    apply Path.ext
    funext s
    exact p.property _ ⟨i.succ, hi⟩

/-- Uncurry the first path coordinate into a based cube. -/
def uncurryLoop {x : X} {n : ℕ} (p : GenLoop (Fin n) (Path x x) (Path.refl x)) :
    GenLoop (Fin (n+1)) X x := by
  refine ⟨⟨fun t => p (Fin.tail t) (t 0), by fun_prop⟩, ?_⟩
  rintro t ⟨i, hi⟩
  cases i using Fin.cases with
  | zero =>
    rcases hi with hi | hi
    · change p (Fin.tail t) (t 0) = x
      rw [hi]; exact (p (Fin.tail t)).source
    · change p (Fin.tail t) (t 0) = x
      rw [hi]; exact (p (Fin.tail t)).target
  | succ i =>
    have he := congrArg (fun q : Path x x => q (t 0)) (p.property (Fin.tail t) ⟨i, hi⟩)
    exact he

theorem uncurry_curryLoop {x : X} {n : ℕ} (p : GenLoop (Fin (n+1)) X x) :
    uncurryLoop (curryLoop p) = p := by
  apply GenLoop.ext
  intro t
  change p (Fin.cons (t 0) (Fin.tail t)) = p t
  rw [Fin.cons_self_tail]

theorem curry_uncurryLoop {x : X} {n : ℕ} (p : GenLoop (Fin n) (Path x x) (Path.refl x)) :
    curryLoop (uncurryLoop p) = p := by
  apply GenLoop.ext
  intro t
  apply Path.ext
  funext s
  rfl

/-- A cubical homotopy curries continuously and remains fixed on the boundary. -/
def curryLoopHomotopy {x : X} {n : ℕ} {p q : GenLoop (Fin (n+1)) X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin (n+1)))) :
    (curryLoop p).val.HomotopyRel (curryLoop q).val (Cube.boundary (Fin n)) := by
  refine ⟨⟨⟨fun a => ⟨⟨fun s => H (a.1, Fin.cons s a.2), by fun_prop⟩, ?_, ?_⟩, ?_⟩,
    ?_, ?_⟩, ?_⟩
  · exact (H.eq_fst _ (show Fin.cons 0 _ ∈ Cube.boundary (Fin (n+1)) from ⟨0, Or.inl rfl⟩)).trans
      (p.property _ ⟨0, Or.inl rfl⟩)
  · exact (H.eq_fst _ (show Fin.cons 1 _ ∈ Cube.boundary (Fin (n+1)) from ⟨0, Or.inr rfl⟩)).trans
      (p.property _ ⟨0, Or.inr rfl⟩)
  · apply Path.continuous_uncurry_iff.mp
    change Continuous (fun a : (unitInterval × (Fin n → unitInterval)) × unitInterval =>
      H (a.1.1, Fin.cons a.2 a.1.2))
    fun_prop
  · intro t; apply Path.ext; funext s; exact H.apply_zero _
  · intro t; apply Path.ext; funext s; exact H.apply_one _
  · rintro t s ⟨i, hi⟩
    apply Path.ext
    funext r
    exact H.eq_fst t (show Fin.cons r s ∈ Cube.boundary (Fin (n+1)) from ⟨i.succ, hi⟩)

/-- Conversely a path-space cubical homotopy uncurries relative to the full boundary. -/
def uncurryLoopHomotopy {x : X} {n : ℕ}
    {p q : GenLoop (Fin n) (Path x x) (Path.refl x)}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin n))) :
    (uncurryLoop p).val.HomotopyRel (uncurryLoop q).val (Cube.boundary (Fin (n+1))) := by
  refine ⟨⟨⟨fun a => H (a.1, Fin.tail a.2) (a.2 0), by fun_prop⟩, ?_, ?_⟩, ?_⟩
  · intro t
    exact congrArg (fun q : Path x x => q (t 0)) (H.apply_zero _)
  · intro t
    exact congrArg (fun q : Path x x => q (t 0)) (H.apply_one _)
  · rintro s t ⟨i, hi⟩
    cases i using Fin.cases with
    | zero =>
      rcases hi with hi | hi
      · change H (s, Fin.tail t) (t 0) = p (Fin.tail t) (t 0)
        rw [hi, (H (s, Fin.tail t)).source, (p (Fin.tail t)).source]
      · change H (s, Fin.tail t) (t 0) = p (Fin.tail t) (t 0)
        rw [hi, (H (s, Fin.tail t)).target, (p (Fin.tail t)).target]
    | succ i =>
      exact congrArg (fun q : Path x x => q (t 0))
        (H.eq_fst s (show Fin.tail t ∈ Cube.boundary (Fin n) from ⟨i, hi⟩))

/-- Dimension shift on the actual homotopy-group quotients. -/
def loopDimensionShift (n : ℕ) (x : X) :
    HomotopyGroup.Pi (n+1) X x ≃ HomotopyGroup.Pi n (Path x x) (Path.refl x) where
  toFun := Quotient.map curryLoop (fun _ _ h => h.map curryLoopHomotopy)
  invFun := Quotient.map uncurryLoop (fun _ _ h => h.map uncurryLoopHomotopy)
  left_inv p := by
    induction p using Quotient.inductionOn with
    | h p => exact congrArg (Quotient.mk _) (uncurry_curryLoop p)
  right_inv p := by
    induction p using Quotient.inductionOn with
    | h p => exact congrArg (Quotient.mk _) (curry_uncurryLoop p)

/-- Dimension shift commutes with the actual induced maps. -/
theorem loopDimensionShift_naturality (f : C(X, Y)) (n : ℕ) (x : X)
    (p : HomotopyGroup.Pi (n+1) X x) :
    loopDimensionShift n (f x) (groupMap f (n+1) x p) =
      basedGroupMap (PathSpace.map f) (show PathSpace.map f (Path.refl x) = Path.refl (f x) from rfl) n (loopDimensionShift n x p) := by
  induction p using Quotient.inductionOn with
  | h p => rfl

end Thomason.Construction.HomotopyMaps

end

end OAI
