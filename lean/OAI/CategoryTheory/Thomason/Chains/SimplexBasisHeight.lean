import OAI.CategoryTheory.Thomason.Chains.FinalPositiveSimplexSupport
import OAI.CategoryTheory.Thomason.Gray.DirectedGlobeUniversal
import OAI.CategoryTheory.Thomason.Gray.OrderedAtomGrouping
import OAI.CategoryTheory.Thomason.Simplicial.LoopDimensionShift

namespace OAI

section

/-! # The chain-cylinder functor

Positive augmentation-preserving chain maps form a category. Realization
and tensoring on the right by the interval are functors, with natural
endpoint inclusions and collapse.
-/

namespace Thomason.Construction.DirectedComplex

open CategoryTheory

noncomputable section

namespace Hom

theorem ext_app {K L : DirectedComplex.{0}} {f g : Hom K L}
    (h : ∀ n x, f.app n x = g.app n x) : f = g := by
  cases f with
  | mk fa fd fe fp =>
    cases g with
    | mk ga gd ge gp =>
      have he : fa = ga := funext (fun n => AddMonoidHom.ext (h n))
      cases he
      rfl

def id (K : DirectedComplex.{0}) : Hom K K where
  app n := AddMonoidHom.id (K.group n)
  differential _ _ := rfl
  augmentation _ := rfl
  positive _ _ h := h

def comp {K L M : DirectedComplex.{0}} (f : Hom K L) (g : Hom L M) : Hom K M where
  app n := (g.app n).comp (f.app n)
  differential n x := by
    change g.app n (f.app n (K.differential n x)) =
      M.differential n (g.app (n+1) (f.app (n+1) x))
    rw [f.differential, g.differential]
  augmentation x := (g.augmentation _).trans (f.augmentation x)
  positive n _ hx := g.positive n (f.positive n hx)

end Hom

instance : Category DirectedComplex.{0} where
  Hom K L := Hom K L
  id := Hom.id
  comp := Hom.comp
  id_comp _ := Hom.ext_app (fun _ _ => rfl)
  comp_id _ := Hom.ext_app (fun _ _ => rfl)
  assoc _ _ _ := Hom.ext_app (fun _ _ => rfl)

/-- Strict realization of positive chain maps is a functor. -/
def realizationFunctor : DirectedComplex.{0} ⥤ StrictOmegaCategory.{0} where
  obj := realization
  map := Hom.realization
  map_id _ := by
    apply StrictOmegaCategory.Hom.ext
    funext x
    apply Cell.ext
    rfl
  map_comp _ _ := by
    apply StrictOmegaCategory.Hom.ext
    funext x
    apply Cell.ext
    rfl

/-- The fixed right interval tensor, with its signed differential. -/
def rightCylinderFunctor : DirectedComplex.{0} ⥤ DirectedComplex.{0} where
  obj := rightCylinder
  map := RightCylinder.map
  map_id _ := by
    apply Hom.ext_app
    intro n x
    cases n <;> rfl
  map_comp _ _ := by
    apply Hom.ext_app
    intro n x
    cases n <;> rfl

/-- The endpoint chain maps are natural in the directed complex. -/
def rightEndpoint (a : Bool) : 𝟭 DirectedComplex.{0} ⟶ rightCylinderFunctor where
  app K := RightCylinder.endpoint K a
  naturality K L f := by
    apply Hom.ext_app
    intro n x
    exact (RightCylinder.map_endpoint f a n x).symm

/-- The interval collapse is a natural positive chain map. -/
def rightProjection : rightCylinderFunctor ⟶ 𝟭 DirectedComplex.{0} where
  app K := RightCylinder.projection K
  naturality K L f := by
    apply Hom.ext_app
    intro n x
    exact RightCylinder.projection_map f n x

theorem rightEndpoint_projection (a : Bool) (K : DirectedComplex.{0}) :
    (rightEndpoint a).app K ≫ rightProjection.app K = 𝟙 K := by
  apply Hom.ext_app
  intro n x
  exact RightCylinder.projection_endpoint K a n x

end

end Thomason.Construction.DirectedComplex

end

section

/-! # Boundedness of positive composites

In a directed complex whose positive monoids have no nonzero additive
inverses, a composite can have dimension at most n only when both factors
do. This prevents higher atoms from disappearing in the simplex chain
presentation, and gives a degreewise inverse to strict abelianization.
-/

namespace Thomason.Construction.DirectedComplex.Cell

open CategoryTheory

universe u

variable {K : DirectedComplex.{u}}

/-- Bounded cells have zero table entries in every higher degree. -/
theorem table_zero_of_dimensionLE {x : K.realization} {n : ℕ}
    (hx : K.realization.DimensionLE n x) {p : ℕ} (hp : n < p) (a : Bool) :
    x.table a p = 0 := by
  have he := congrArg (fun z : Cell K => z.table a p) hx.1
  change cutTable x false n a p = x.table a p at he
  simpa only [cutTable, Nat.not_lt.mpr hp.le, Nat.ne_of_gt hp, ite_false] using he.symm

/-- Vanishing above n determines the equal top entries by the boundary equation. -/
theorem dimensionLE_of_table_zero {x : K.realization} {n : ℕ}
    (hx : ∀ p, n < p → ∀ a, x.table a p = 0) : K.realization.DimensionLE n x := by
  have ht : x.table true n = x.table false n := by
    have hb := x.boundary false n
    rw [hx (n+1) (Nat.lt_succ_self n) false, map_zero] at hb
    exact sub_eq_zero.mp hb.symm
  have hf (a : Bool) : x.face a n = x := by
    apply Cell.ext
    funext b p
    change cutTable x a n b p = x.table b p
    by_cases hp : p < n
    · simp only [cutTable, hp, ite_true]
    · by_cases he : p = n
      · subst p
        cases a <;> cases b <;> simp only [cutTable, Nat.lt_irrefl, ite_false, ite_true]
        · exact ht.symm
        · exact ht
      · simp only [cutTable, hp, he, ite_false]
        exact (hx p (by omega) b).symm
  exact ⟨hf false, hf true⟩

/-- Positivity rules out cancellation of higher cells in a composite. -/
theorem dimensionLE_comp_factors
    (hpos : ∀ p (a b : K.group p), a ∈ K.positive p → b ∈ K.positive p →
      a + b = 0 → a = 0 ∧ b = 0)
    {x y : K.realization} {k n : ℕ}
    (hxy : K.realization.target k x = K.realization.source k y)
    (hc : K.realization.DimensionLE n (K.realization.comp k x y hxy)) :
    K.realization.DimensionLE n x ∧ K.realization.DimensionLE n y := by
  have hz {p : ℕ} (hnp : n < p) (hkp : k < p) (a : Bool) :
      x.table a p = 0 ∧ y.table a p = 0 := by
    have he := table_zero_of_dimensionLE hc hnp a
    change pasteTable x y k a p = 0 at he
    simp only [pasteTable, Nat.not_lt.mpr hkp.le, Nat.ne_of_gt hkp, ite_false] at he
    exact hpos p _ _ (x.positive a p) (y.positive a p) he
  by_cases hkn : k < n
  · exact ⟨dimensionLE_of_table_zero (fun p hp a => (hz hp (hkn.trans hp) a).1),
      dimensionLE_of_table_zero (fun p hp a => (hz hp (hkn.trans hp) a).2)⟩
  · have hnk : n ≤ k := Nat.le_of_not_gt hkn
    have hx : K.realization.DimensionLE k x :=
      dimensionLE_of_table_zero (fun p hp a => (hz (hnk.trans_lt hp) hp a).1)
    have hy : K.realization.DimensionLE k y :=
      dimensionLE_of_table_zero (fun p hp a => (hz (hnk.trans_lt hp) hp a).2)
    have hc' := K.realization.dimensionLE_mono hnk hc
    have ex : K.realization.comp k x y hxy = x :=
      hc'.1.symm.trans ((K.realization.source_comp k x y hxy).trans hx.1)
    have ey : K.realization.comp k x y hxy = y :=
      hc'.2.symm.trans ((K.realization.target_comp k x y hxy).trans hy.2)
    exact ⟨ex ▸ hc, ey ▸ hc⟩

end Thomason.Construction.DirectedComplex.Cell

end

section

/-! # Dimensionwise expressions over positive atoms

Composition expressions retain their generator occurrences. Positivity of
their image in a complex with an ordered atom basis prevents a generator
of higher degree from disappearing. Composition generation
by bounded atom lifts therefore gives dimensionwise composition
generation in the sense of Steiner 2004, Definition 4.1.
-/

namespace Thomason.Construction.StrictOmegaCategory

open CategoryTheory _root_.OAI.Thomason.Construction.DirectedComplex

/-- A finite, well-typed expression using generators and strict composition. -/
inductive CompositionExpression (C : StrictOmegaCategory.{0}) {I : Type} (g : I → C) :
    C → Type
  | generator (i : I) : CompositionExpression C g (g i)
  | comp {x y : C} (r : ℕ) (hxy : C.target r x = C.source r y)
      (tx : CompositionExpression C g x) (ty : CompositionExpression C g y) :
      CompositionExpression C g (C.comp r x y hxy)

namespace CompositionExpression

variable {C : StrictOmegaCategory.{0}} {I : Type} {g : I → C}

/-- Generator occurrences, with multiplicity and order retained. -/
def labels {x : C} : CompositionExpression C g x → List I
  | .generator i => [i]
  | .comp _ _ tx ty => tx.labels ++ ty.labels

theorem labels_nonempty {x : C} (t : CompositionExpression C g x) : t.labels ≠ [] := by
  induction t with
  | generator i => simp [labels]
  | comp r hxy tx ty hx hy =>
    intro h
    exact hx (List.append_eq_nil_iff.mp h).1

/-- If every occurring generator is bounded, so is the composite. -/
theorem dimensionLE {x : C} (t : CompositionExpression C g x) (d : I → ℕ)
    (hg : ∀ i, C.DimensionLE (d i) (g i)) (n : ℕ)
    (hlabels : ∀ i ∈ t.labels, d i ≤ n) : C.DimensionLE n x := by
  induction t with
  | generator i => exact C.dimensionLE_mono (hlabels i (by simp [labels])) (hg i)
  | comp r hxy tx ty ihx ihy =>
    apply C.dimensionLE_comp_all
    · exact ihx (fun i hi => hlabels i (List.mem_append_left _ hi))
    · exact ihy (fun i hi => hlabels i (List.mem_append_right _ hi))

end CompositionExpression

end Thomason.Construction.StrictOmegaCategory

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

open CategoryTheory StrictOmegaCategory

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

include B

/-- Ordered-basis positivity admits no additive cancellation. -/
theorem positive_add_eq_zero (p : ℕ) (x y : K.group p)
    (hx : x ∈ K.positive p) (hy : y ∈ K.positive p) (h : x + y = 0) :
    x = 0 ∧ y = 0 := by
  have he (b : B.Index p) : B.coordinates p x b + B.coordinates p y b = 0 := by
    have hh := congrArg (fun z => B.coordinates p z b) h
    simpa only [map_add, map_zero, Finsupp.add_apply, Finsupp.zero_apply] using hh
  have hx0 (b : B.Index p) : B.coordinates p x b = 0 := by
    have hp := B.coordinate_nonnegative p x hx b
    have hq := B.coordinate_nonnegative p y hy b
    have hh := he b
    omega
  have hy0 (b : B.Index p) : B.coordinates p y b = 0 := by
    have hh := he b
    rw [hx0 b, zero_add] at hh
    exact hh
  constructor
  · apply (B.coordinates p).injective
    ext b
    simpa only [map_zero, Finsupp.zero_apply] using hx0 b
  · apply (B.coordinates p).injective
    ext b
    simpa only [map_zero, Finsupp.zero_apply] using hy0 b

/-- The nonzero top chain detects the degree of a genuine basis atom. -/
theorem atom_degree_le {p n : ℕ} (b : B.Index p)
    (h : K.realization.DimensionLE n (B.atom p b)) : p ≤ n := by
  by_contra hn
  have hz := Cell.table_zero_of_dimensionLE h (show n < p by omega) false
  have he := congrArg (fun z => B.coordinates p z b) hz
  rw [B.atom_top, map_zero, Finsupp.single_eq_same, Finsupp.zero_apply] at he
  omega

/-- No generator above degree n can occur in an expression whose image is
n-dimensional. This uses positivity rather than injectivity of the map. -/
theorem expression_labels_bounded {C : StrictOmegaCategory.{0}}
    (g : B.AtomIndex → C) (F : C ⟶ K.realization)
    (hg : ∀ i, F.toFun (g i) = B.atomCell i)
    {x : C} (t : CompositionExpression C g x) (n : ℕ)
    (hx : K.realization.DimensionLE n (F.toFun x)) :
    ∀ i ∈ t.labels, i.1 ≤ n := by
  induction t with
  | generator i =>
    intro j hj
    have he : j = i := by simpa only [CompositionExpression.labels, List.mem_singleton] using hj
    subst j
    rw [hg i] at hx
    exact B.atom_degree_le i.2 hx
  | @comp x y r hxy tx ty ihx ihy =>
    have hf : K.realization.target r (F.toFun x) = K.realization.source r (F.toFun y) :=
      (F.map_face true r x).symm.trans
        ((congrArg F.toFun hxy).trans (F.map_face false r y))
    have hc : K.realization.DimensionLE n
        (K.realization.comp r (F.toFun x) (F.toFun y) hf) := by
      rw [← F.map_comp r x y hxy hf]
      exact hx
    obtain ⟨hxx, hyy⟩ := Cell.dimensionLE_comp_factors (B.positive_add_eq_zero) hf hc
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact ihx hxx i hi
    · exact ihy hyy i hi

/-- On a composition-generated source with bounded atom lifts, the
positive-table map reflects every finite dimension bound. -/
theorem dimensionLE_of_expression_image {C : StrictOmegaCategory.{0}}
    (g : B.AtomIndex → C) (F : C ⟶ K.realization)
    (hg : ∀ i, F.toFun (g i) = B.atomCell i)
    (hd : ∀ i, C.DimensionLE i.1 (g i))
    {x : C} (t : CompositionExpression C g x) (n : ℕ)
    (hx : K.realization.DimensionLE n (F.toFun x)) : C.DimensionLE n x :=
  t.dimensionLE (fun i => i.1) hd n (B.expression_labels_bounded g F hg t n hx)

/-- Ordinary composition generation by atom lifts is dimensionwise:
an n-cell has an expression using only the generators of degree at most n. -/
theorem exists_bounded_expression {C : StrictOmegaCategory.{0}}
    (g : B.AtomIndex → C) (F : C ⟶ K.realization)
    (hg : ∀ i, F.toFun (g i) = B.atomCell i)
    (hgen : ∀ x : C, Nonempty (CompositionExpression C g x))
    (n : ℕ) (x : C) (hx : C.DimensionLE n x) :
    ∃ t : CompositionExpression C g x, ∀ i ∈ t.labels, i.1 ≤ n := by
  obtain ⟨t⟩ := hgen x
  exact ⟨t, B.expression_labels_bounded g F hg t n (F.dimensionLE hx)⟩

end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

section

/-! # Chain maps agree after mapping into a truncated strict category

Agreement of directed chain maps through degree n gives equal n-faces
on every positive table. A strict functor to an n-truncated target then
identifies the complete cells. No generation or freeness theorem is used.
-/

namespace Thomason.Construction.DirectedComplex

open CategoryTheory

universe u

variable {K L : DirectedComplex.{u}}

/-- Low-degree agreement fixes every chosen n-face of the images. -/
theorem realization_face_eq_of_agree_through
    (f g : Hom K L) {n : ℕ} (hfg : ∀ k, k ≤ n → f.app k = g.app k)
    (a : Bool) (x : K.realization) :
    L.realization.face a n (f.realization x) =
      L.realization.face a n (g.realization x) := by
  apply Cell.ext
  funext b k
  change Cell.cutTable (Cell.map f x) a n b k = Cell.cutTable (Cell.map g x) a n b k
  by_cases hkn : k < n
  · simp only [Cell.cutTable, hkn, ite_true]
    change f.app k (x.table b k) = g.app k (x.table b k)
    rw [hfg k hkn.le]
  · by_cases he : k = n
    · subst k
      simp only [Cell.cutTable, Nat.lt_irrefl, ite_false, ite_true]
      change f.app n (x.table a n) = g.app n (x.table a n)
      rw [hfg n le_rfl]
    · simp only [Cell.cutTable, hkn, he, ite_false]

/-- Any strict functor to an n-truncated target identifies directed chain
maps which agree through degree n. -/
theorem realization_comp_eq_of_agree_through
    (f g : Hom K L) {n : ℕ} (hfg : ∀ k, k ≤ n → f.app k = g.app k)
    {Y : StrictOmegaCategory.{u}} (hY : Y.IsTruncated n) (H : L.realization ⟶ Y) :
    f.realization ≫ H = g.realization ≫ H := by
  apply StrictOmegaCategory.Hom.ext
  funext x
  have hface (z : L.realization) : H.toFun (L.realization.face false n z) = H.toFun z :=
    (H.map_face false n z).trans (hY (H.toFun z)).1
  exact (hface (f.realization x)).symm.trans
    ((congrArg H.toFun (realization_face_eq_of_agree_through f g hfg false x)).trans
      (hface (g.realization x)))

/-- Tensoring with the right interval preserves degreewise agreement
through the same bound. -/
theorem rightCylinderMap_agree_through
    (f g : Hom K L) {n : ℕ} (hfg : ∀ k, k ≤ n → f.app k = g.app k) :
    ∀ k, k ≤ n → (RightCylinder.map f).app k = (RightCylinder.map g).app k := by
  intro k hk
  apply AddMonoidHom.ext
  intro x
  cases k with
  | zero =>
    change (f.app 0 x.1, f.app 0 x.2) = (g.app 0 x.1, g.app 0 x.2)
    rw [hfg 0 hk]
  | succ k =>
    change (f.app (k+1) x.1, f.app (k+1) x.2.1, f.app k x.2.2) =
      (g.app (k+1) x.1, g.app (k+1) x.2.1, g.app k x.2.2)
    rw [hfg (k+1) hk, hfg k ((Nat.le_succ k).trans hk)]

/-- The corresponding exact comparison for right-cylinder realizations. -/
theorem rightCylinder_realization_comp_eq_of_agree_through
    (f g : Hom K L) {n : ℕ} (hfg : ∀ k, k ≤ n → f.app k = g.app k)
    {Y : StrictOmegaCategory.{u}} (hY : Y.IsTruncated n)
    (H : (rightCylinder L).realization ⟶ Y) :
    (RightCylinder.map f).realization ≫ H = (RightCylinder.map g).realization ≫ H :=
  realization_comp_eq_of_agree_through _ _ (rightCylinderMap_agree_through f g hfg) hY H

end Thomason.Construction.DirectedComplex

end

section

/-! # Positive chain bridges detect equality in truncated targets

An explicit positive chain in degree n+1 joins prescribed n-faces. Such a
bridge is killed by every strict functor into an n-truncated category.
This allows degree-n maps to differ by a positive boundary.
-/

namespace Thomason.Construction.DirectedComplex

open CategoryTheory

universe u

namespace Cell

variable {K : DirectedComplex.{u}} (x y : Cell K) (n : ℕ)
    (z : K.group (n+1))

def bridgeTable (a : Bool) (k : ℕ) : K.group k :=
  if k ≤ n then if a then y.table true k else x.table false k
  else if h : k = n+1 then h.symm ▸ z else 0

/-- A positive (n+1)-chain and common lower faces form a literal cell. -/
def bridge (hz : z ∈ K.positive (n+1))
    (hxy : ∀ k, k < n → ∀ a, x.table a k = y.table a k)
    (hd : K.differential n z = y.table true n - x.table false n) : Cell K where
  table := bridgeTable x y n z
  positive a k := by
    unfold bridgeTable
    split_ifs with hk he
    · exact y.positive true k
    · exact x.positive false k
    · subst k
      exact hz
    · exact (K.positive k).zero_mem
  augmentation a := by
    cases a <;> simp only [bridgeTable, Nat.zero_le, ite_true, Bool.false_eq_true,
      ite_false, x.augmentation, y.augmentation]
  boundary a k := by
    by_cases hkn : k < n
    · have hk : k ≤ n := hkn.le
      have hk' : k+1 ≤ n := hkn
      cases a <;> simp only [bridgeTable, hk, hk', ite_true, Bool.false_eq_true, ite_false]
      · rw [x.boundary, hxy k hkn true]
      · rw [y.boundary, hxy k hkn false]
    · by_cases he : k = n
      · subst k
        have hn : ¬n+1 ≤ n := Nat.not_succ_le_self n
        cases a <;> simpa [bridgeTable, hn] using hd
      · have hk : ¬k ≤ n := by omega
        have hk' : ¬k+1 ≤ n := by omega
        simp [bridgeTable, hk, hk', he]
  finite_support := ⟨n+1, fun k hk a => by
    have hkn : ¬k ≤ n := by omega
    have hkne : k ≠ n+1 := by omega
    simp [bridgeTable, hkn, hkne]⟩

/-- The new cell has exactly the prescribed source n-face. -/
theorem bridge_source (hz hxy hd) :
    (bridge x y n z hz hxy hd).face false n = x.face false n := by
  apply Cell.ext
  funext a k
  by_cases hk : k < n
  · simp only [face_table, cutTable, hk, ite_true, bridge, bridgeTable, hk.le]
    cases a
    · rfl
    · exact (hxy k hk true).symm
  · by_cases he : k = n
    · subst k
      simp only [face_table, cutTable, Nat.lt_irrefl, ite_false, ite_true,
        bridge, bridgeTable, le_refl, Bool.false_eq_true]
    · simp only [face_table, cutTable, hk, he, ite_false]

/-- The new cell has exactly the prescribed target n-face. -/
theorem bridge_target (hz hxy hd) :
    (bridge x y n z hz hxy hd).face true n = y.face true n := by
  apply Cell.ext
  funext a k
  by_cases hk : k < n
  · simp only [face_table, cutTable, hk, ite_true, bridge, bridgeTable, hk.le]
    cases a
    · exact hxy k hk false
    · rfl
  · by_cases he : k = n
    · subst k
      simp only [face_table, cutTable, Nat.lt_irrefl, ite_false, ite_true,
        bridge, bridgeTable, le_refl]
    · simp only [face_table, cutTable, hk, he, ite_false]

end Cell

/-- Positive degree-(n+1) bridges suffice when the chain maps agree only
strictly below n. This is stronger than agreement through degree n. -/
theorem realization_comp_eq_of_positive_degree_bridge
    {K L : DirectedComplex.{u}} (f g : Hom K L) {n : ℕ}
    (hfg : ∀ k, k < n → f.app k = g.app k)
    (hbridge : ∀ v : K.group n, v ∈ K.positive n →
      ∃ z : L.group (n+1), z ∈ L.positive (n+1) ∧
        L.differential n z = g.app n v - f.app n v)
    {Y : StrictOmegaCategory.{u}} (hY : Y.IsTruncated n) (H : L.realization ⟶ Y) :
    f.realization ≫ H = g.realization ≫ H := by
  apply StrictOmegaCategory.Hom.ext
  funext x
  obtain ⟨z, hz, hdz⟩ := hbridge (x.table false n) (x.positive false n)
  let z' := g.app (n+1) (x.table false (n+1)) + z
  have hz' : z' ∈ L.positive (n+1) :=
    (L.positive (n+1)).add_mem (g.positive _ (x.positive _ _)) hz
  have hxy : ∀ k, k < n → ∀ a,
      (Cell.map f x).table a k = (Cell.map g x).table a k := by
    intro k hk a
    change f.app k (x.table a k) = g.app k (x.table a k)
    rw [hfg k hk]
  have hd' : L.differential n z' =
      (Cell.map g x).table true n - (Cell.map f x).table false n := by
    change L.differential n (g.app (n+1) (x.table false (n+1)) + z) =
      g.app n (x.table true n) - f.app n (x.table false n)
    rw [map_add, ← g.differential, x.boundary, map_sub, hdz]
    abel
  let b := Cell.bridge (Cell.map f x) (Cell.map g x) n z' hz' hxy hd'
  have hs : b.face false n = (Cell.map f x).face false n :=
    Cell.bridge_source _ _ _ _ hz' hxy hd'
  have ht : b.face true n = (Cell.map g x).face true n :=
    Cell.bridge_target _ _ _ _ hz' hxy hd'
  have hface (c : L.realization) (a : Bool) :
      H.toFun (c.face a n) = H.toFun c := by
    exact (H.map_face a n c).trans (by cases a; exact (hY _).1; exact (hY _).2)
  calc
    H.toFun (Cell.map f x) = H.toFun ((Cell.map f x).face false n) := (hface _ false).symm
    _ = H.toFun (b.face false n) := congrArg H.toFun hs.symm
    _ = H.toFun b := hface b false
    _ = H.toFun (b.face true n) := (hface b true).symm
    _ = H.toFun ((Cell.map g x).face true n) := congrArg H.toFun ht
    _ = H.toFun (Cell.map g x) := hface _ true

end Thomason.Construction.DirectedComplex

end

section

/-! # A finite height for signed simplex faces

The alternating ternary height puts every negative boundary basis below
its simplex and every positive boundary basis above it. These finite
inequalities are the ordering input for the remaining atom decomposition.
-/

namespace Thomason.Construction.SimplexComplex

/-- Weights are listed in strictly decreasing order. -/
def alternatingHeight : List ℕ → ℤ
  | [] => 0
  | w :: ws => -(3 : ℤ)^w - alternatingHeight ws

/-- The leading ternary weight controls the entire alternating tail. -/
theorem alternatingHeight_bounds {w : ℕ} {ws : List ℕ}
    (hs : (w :: ws).Pairwise (· > ·)) :
    -(3 : ℤ)^w ≤ alternatingHeight (w :: ws) ∧
      alternatingHeight (w :: ws) < 0 := by
  induction ws generalizing w with
  | nil =>
    have hp : 0 < (3 : ℤ)^w := pow_pos (by norm_num) _
    simp only [alternatingHeight]
    constructor <;> omega
  | cons v vs ih =>
    obtain ⟨hw, ht⟩ := List.pairwise_cons.mp hs
    obtain ⟨hb, hn⟩ := ih ht
    have hvw : v < w := hw v (by simp)
    have hp : (3 : ℤ)^v < 3^w := pow_lt_pow_right₀ (by norm_num) hvw
    change -(3 : ℤ)^w ≤ -(3 : ℤ)^w - alternatingHeight (v :: vs) ∧
      -(3 : ℤ)^w - alternatingHeight (v :: vs) < 0
    constructor <;> omega

/-- Removing the leading vertex strictly increases the height. The factor
three leaves room for both copies of every remaining signed tail. -/
theorem alternatingHeight_remove_head {w : ℕ} {ws : List ℕ}
    (hs : (w :: ws).Pairwise (· > ·)) :
    0 < alternatingHeight ws - alternatingHeight (w :: ws) := by
  cases ws with
  | nil =>
    simp [alternatingHeight]
  | cons v vs =>
    obtain ⟨hw, ht⟩ := List.pairwise_cons.mp hs
    have hvw : v < w := hw v (by simp)
    have hb := (alternatingHeight_bounds ht).1
    have hp : (3 : ℤ)^(v+1) ≤ 3^w :=
      pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt hvw)
    have hpos : 0 < (3 : ℤ)^v := pow_pos (by norm_num) _
    rw [pow_succ] at hp
    change 0 < alternatingHeight (v :: vs) -
      (-(3 : ℤ)^w - alternatingHeight (v :: vs))
    omega

/-- Deleting position i changes height with exactly the boundary sign
(-1)^i. In particular no signed boundary relation can form a cycle. -/
theorem alternatingHeight_eraseIdx (ws : List ℕ) (hs : ws.Pairwise (· > ·))
    (i : ℕ) (hi : i < ws.length) :
    0 < (-1 : ℤ)^i * (alternatingHeight (ws.eraseIdx i) - alternatingHeight ws) := by
  induction ws generalizing i with
  | nil => simp at hi
  | cons w ws ih =>
    cases i with
    | zero => simpa using alternatingHeight_remove_head hs
    | succ i =>
      have hh := ih (List.pairwise_cons.mp hs).2 i (by simpa using hi)
      calc
        _ = (-1 : ℤ)^i * (alternatingHeight (ws.eraseIdx i) - alternatingHeight ws) := by
          simp only [List.eraseIdx_cons_succ, alternatingHeight, pow_succ]
          ring
        _ > 0 := hh

end Thomason.Construction.SimplexComplex

end

end OAI
