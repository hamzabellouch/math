import OAI.CategoryTheory.Thomason.Chains.DirectedComplex
import OAI.CategoryTheory.Thomason.Strict.StrictCompositeListReplacement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Order.Fin.Basic

namespace OAI

section

/-!
# Realizing directed complexes as strict omega-categories

The finite positive tables form a strict omega-category. Composition
adds the higher chains and uses the exterior source and target chains.
The globular, unit, associative and interchange laws are proved on tables.
-/

namespace Thomason.Construction.DirectedComplex

universe u

namespace Cell

variable {K : DirectedComplex.{u}}

theorem source_comp (x y : Cell K) (n : ℕ) (h) :
    (comp x y n h).face false n = x.face false n := by
  ext a m
  simp only [face_table, cutTable, comp_table, pasteTable, Bool.false_eq_true, ite_false]
  split_ifs <;> rfl

theorem target_comp (x y : Cell K) (n : ℕ) (h) :
    (comp x y n h).face true n = y.face true n := by
  ext a m
  by_cases hm : m < n
  · simp only [face_table, cutTable, comp_table, pasteTable, hm, ite_true]
    exact matching_below h a hm
  · simp only [face_table, cutTable, comp_table, pasteTable, hm, ite_false]
    split_ifs <;> rfl

theorem left_unit (x : Cell K) (n : ℕ) (h) : comp (x.face false n) x n h = x := by
  ext a m
  by_cases hm : m < n
  · simp only [comp_table, pasteTable, face_table, cutTable, hm, ite_true]
  · by_cases he : m = n
    · subst m
      cases a <;> simp [comp_table, pasteTable, face_table, cutTable]
    · simp only [comp_table, pasteTable, face_table, cutTable,
        hm, he, ite_false, zero_add]

theorem right_unit (x : Cell K) (n : ℕ) (h) : comp x (x.face true n) n h = x := by
  ext a m
  by_cases hm : m < n
  · simp only [comp_table, pasteTable, hm, ite_true]
  · by_cases he : m = n
    · subst m
      cases a <;> simp [comp_table, pasteTable, face_table, cutTable]
    · simp only [comp_table, pasteTable, face_table, cutTable,
        hm, he, ite_false, add_zero]

theorem assoc (x y z : Cell K) (n : ℕ) (hxy hyz hl hr) :
    comp (comp x y n hxy) z n hl = comp x (comp y z n hyz) n hr := by
  ext a m
  simp only [comp_table, pasteTable]
  split_ifs <;> (try contradiction) <;> (try rfl)
  all_goals exact add_assoc _ _ _

theorem face_comp (x y : Cell K) (n m : ℕ) (hnm : n < m) (a : Bool) (h h') :
    (comp x y n h).face a m = comp (x.face a m) (y.face a m) n h' := by
  ext b k
  simp only [face_table, cutTable, comp_table, pasteTable]
  split_ifs <;> (try rfl)
  all_goals simp_all

theorem interchange (a b c d : Cell K) (m n : ℕ) (hmn : m < n)
    (hab hcd hac hbd hl hr) :
    comp (comp a b m hab) (comp c d m hcd) n hl =
      comp (comp a c n hac) (comp b d n hbd) m hr := by
  ext e k
  simp only [comp_table, pasteTable]
  split_ifs <;> (try rfl)
  all_goals first | omega | abel

/-- Finite support supplies a dimension bound: the top positive and negative
chains coincide because the next chain vanishes. -/
theorem finite_dimension (x : Cell K) : ∃ n, x.face false n = x ∧ x.face true n = x := by
  obtain ⟨N, hN⟩ := x.finite_support
  have ht : x.table true N = x.table false N := by
    apply sub_eq_zero.mp
    rw [← x.boundary false N, hN (N + 1) (Nat.lt_succ_self N) false, map_zero]
  have hf (a : Bool) : x.face a N = x := by
    ext b m
    by_cases hm : m < N
    · simp only [face_table, cutTable, hm, ite_true]
    · by_cases he : m = N
      · subst m
        cases a <;> cases b <;>
          simp only [face_table, cutTable, Nat.lt_irrefl, ite_false, ite_true, ht]
      · have hNm : N < m := by omega
        simp only [face_table, cutTable, hm, he, ite_false, hN m hNm b]
  exact ⟨N, hf false, hf true⟩

end Cell

/-- Steiner's positive-table construction as a strict omega-category. -/
def realization (K : DirectedComplex.{u}) : StrictOmegaCategory.{u} where
  Cell := Cell K
  face a n x := x.face a n
  globular a b m n x := Cell.face_face x a b m n
  comp n x y h := Cell.comp x y n h
  source_comp n x y h := Cell.source_comp x y n h
  target_comp n x y h := Cell.target_comp x y n h
  face_comp a m n hnm x y h h' := Cell.face_comp x y n m hnm a h h'
  left_unit n x h := Cell.left_unit x n h
  right_unit n x h := Cell.right_unit x n h
  assoc n x y z hxy hyz hl hr := Cell.assoc x y z n hxy hyz hl hr
  interchange m n hmn a b c d hab hcd hac hbd hl hr :=
    Cell.interchange a b c d m n hmn hab hcd hac hbd hl hr
  finite_dimension := Cell.finite_dimension

/-- A positive augmentation-preserving chain map gives a strict functor. -/
def Hom.realization {K L : DirectedComplex.{u}} (f : Hom K L) :
    StrictOmegaCategory.Hom K.realization L.realization where
  toFun := Cell.map f
  map_face a n x := Cell.map_face f x a n
  map_comp n x y h h' := Cell.map_comp f x y n h h'

end Thomason.Construction.DirectedComplex

end

section

/-! # Dimension bounds of positive tables

A strict dimension bound is exactly vanishing of the chain table above
that degree. This relates globular truncation to chain support.
-/

namespace Thomason.Construction.DirectedComplex.Cell

variable {K : DirectedComplex.{0}}

theorem dimensionLE_iff_zero_above (x : Cell K) (n : ℕ) :
    K.realization.DimensionLE n x ↔ ∀ k, n < k → ∀ a, x.table a k = 0 := by
  constructor
  · intro hx k hk a
    have h := congrArg (fun y : Cell K => y.table a k) hx.1
    change cutTable x false n a k = x.table a k at h
    simpa only [cutTable, Nat.not_lt.mpr hk.le, Nat.ne_of_gt hk, ite_false] using h.symm
  · intro hx
    have ht : x.table true n = x.table false n := by
      apply sub_eq_zero.mp
      rw [← x.boundary false n, hx (n+1) (Nat.lt_succ_self n) false, map_zero]
    have hf (a : Bool) : x.face a n = x := by
      apply Cell.ext
      funext b k
      change cutTable x a n b k = x.table b k
      by_cases hk : k < n
      · simp only [cutTable, hk, ite_true]
      · by_cases he : k = n
        · subst k
          cases a <;> cases b <;> simp only [cutTable, Nat.lt_irrefl, ite_false,
            ite_true, ht]
        · have hnk : n < k := by omega
          simp only [cutTable, hk, he, ite_false, hx k hnk b]
    exact ⟨hf false, hf true⟩

end Thomason.Construction.DirectedComplex.Cell

end

section

/-! # Positive binary decomposition of a globular table

This is the binary table construction in Steiner 2004, Proposition 5.1.
A positive middle chain determines the cell, matching, and composition
equations without a generation hypothesis.
-/

namespace Thomason.Construction.DirectedComplex.Cell

universe u

variable {K : DirectedComplex.{u}}

/-- A finite positive table with a common augmentation on its two sides.
Sums of atoms have this form even when their augmentation exceeds one. -/
structure PositiveTable (K : DirectedComplex.{u}) where
  table (a : Bool) (n : ℕ) : K.group n
  positive (a : Bool) (n : ℕ) : table a n ∈ K.positive n
  augmentation (a : Bool) : K.augmentation (table a 0) = K.augmentation (table false 0)
  boundary (a : Bool) (n : ℕ) :
    K.differential n (table a (n+1)) = table true n - table false n
  finite_support : ∃ N, ∀ n, N < n → ∀ a, table a n = 0

namespace PositiveTable

/-- Globular cells are the augmentation-one positive tables. -/
def ofCell (x : Cell K) : PositiveTable K where
  table := x.table
  positive := x.positive
  augmentation a := by rw [x.augmentation a, x.augmentation false]
  boundary := x.boundary
  finite_support := x.finite_support

instance : Coe (Cell K) (PositiveTable K) := ⟨ofCell⟩

/-- Positive tables add without an artificial augmentation-one restriction. -/
def add (A B : PositiveTable K) : PositiveTable K where
  table a n := A.table a n + B.table a n
  positive a n := (K.positive n).add_mem (A.positive a n) (B.positive a n)
  augmentation a := by rw [map_add, map_add, A.augmentation a, B.augmentation a]
  boundary a n := by rw [map_add, A.boundary, B.boundary]; abel
  finite_support := by
    obtain ⟨N, hN⟩ := A.finite_support
    obtain ⟨M, hM⟩ := B.finite_support
    refine ⟨max N M, ?_⟩
    intro n hn a
    rw [hN n (lt_of_le_of_lt (Nat.le_max_left _ _) hn) a,
      hM n (lt_of_le_of_lt (Nat.le_max_right _ _) hn) a, zero_add]

def zero : PositiveTable K where
  table _ _ := 0
  positive _ _ := (K.positive _).zero_mem
  augmentation _ := rfl
  boundary _ _ := by rw [map_zero, sub_self]
  finite_support := ⟨0, fun _ _ _ => rfl⟩

/-- Finite sums of atoms are positive tables. -/
def ofCells : List (Cell K) → PositiveTable K
  | [] => zero
  | A :: as => add (ofCell A) (ofCells as)

@[simp] theorem ofCells_table (as : List (Cell K)) (side : Bool) (n : ℕ) :
    (ofCells as).table side n = (as.map (fun A => A.table side n)).sum := by
  induction as with
  | nil => rfl
  | cons A as ih =>
    change A.table side n + (ofCells as).table side n = _
    simpa only [List.map_cons, List.sum_cons] using congrArg (A.table side n + ·) ih

end PositiveTable

/-- Replace the upper part of X by A and retain one chosen r-boundary of X. -/
def replacementTable (X : Cell K) (A : PositiveTable K) (r : ℕ) (side a : Bool) (n : ℕ) : K.group n :=
  if n < r then X.table a n else if n = r then
    X.table side n + A.table a n - A.table side n else A.table a n

/-- A positive middle boundary suffices to make the replacement a
strict globular cell, with every lower boundary equation retained. -/
def replacement (X : Cell K) (A : PositiveTable K) (r : ℕ) (side : Bool)
    (hpos : ∀ a, X.table side r + A.table a r - A.table side r ∈ K.positive r) :
    Cell K where
  table := replacementTable X A r side
  positive a n := by
    unfold replacementTable
    split_ifs with hn he
    · exact X.positive a n
    · subst n
      exact hpos a
    · exact A.positive a n
  augmentation a := by
    by_cases hr : r = 0
    · subst r
      simp only [replacementTable, Nat.lt_irrefl, ite_false, ite_true,
        map_sub, map_add, X.augmentation, A.augmentation]
      norm_num
    · have hr' : 0 < r := Nat.pos_of_ne_zero hr
      simpa only [replacementTable, hr', ite_true] using X.augmentation a
  boundary a n := by
    by_cases hnr : n+1 < r
    · have hn : n < r := by omega
      simpa only [replacementTable, hnr, hn, ite_true] using X.boundary a n
    · by_cases he : n+1 = r
      · subst r
        have hn : n < n+1 := Nat.lt_succ_self n
        simp only [replacementTable, hn, Nat.lt_irrefl, ite_false, ite_true,
          map_sub, map_add, X.boundary, A.boundary]
        abel
      · have hnr' : r ≤ n := by omega
        by_cases he' : n = r
        · subst n
          simp only [replacementTable, Nat.lt_irrefl, Nat.not_lt.mpr (Nat.le_succ r),
            Nat.succ_ne_self, ite_false, ite_true, A.boundary]
          abel
        · have hn : ¬ n < r := Nat.not_lt.mpr hnr'
          simpa only [replacementTable, hnr, he, hn, he', ite_false] using A.boundary a n
  finite_support := by
    obtain ⟨N, hN⟩ := A.finite_support
    refine ⟨max r N, ?_⟩
    intro n hn a
    have hrn : r < n := lt_of_le_of_lt (Nat.le_max_left r N) hn
    have hNn : N < n := lt_of_le_of_lt (Nat.le_max_right r N) hn
    simp only [replacementTable, Nat.not_lt.mpr hrn.le, Nat.ne_of_gt hrn,
      ite_false, hN n hNn a]

@[simp] theorem replacement_table (X : Cell K) (A : PositiveTable K) (r : ℕ) (side : Bool)
    (hpos : ∀ a, X.table side r + A.table a r - A.table side r ∈ K.positive r)
    (a : Bool) (n : ℕ) :
    (replacement X A r side hpos).table a n = replacementTable X A r side a n := rfl

/-- The difference of the two r-boundaries is additive whenever the next
table is additive. -/
theorem boundary_add_of_above (X : Cell K) (A B : PositiveTable K) (r : ℕ)
    (he : X.table false (r+1) = A.table false (r+1) + B.table false (r+1)) :
    X.table true r - X.table false r =
      (A.table true r - A.table false r) + (B.table true r - B.table false r) := by
  have hh := congrArg (K.differential r) he
  simpa only [map_add, X.boundary, A.boundary, B.boundary] using hh

/-- The two formulas for the joining chain agree. -/
theorem replacement_middle_eq (X : Cell K) (A B : PositiveTable K) (r : ℕ)
    (he : X.table false (r+1) = A.table false (r+1) + B.table false (r+1)) :
    X.table false r + A.table true r - A.table false r =
      X.table true r + B.table false r - B.table true r := by
  have hh := boundary_add_of_above X A B r he
  apply sub_eq_zero.mp
  calc
    _ = (A.table true r - A.table false r) + (B.table true r - B.table false r) -
        (X.table true r - X.table false r) := by abel
    _ = 0 := by rw [hh, sub_self]

/-- Binary table decomposition with an explicitly positive joining chain. -/
theorem exists_comp_of_positive_middle (X : Cell K) (A B : PositiveTable K) (r : ℕ)
    (he : ∀ n, r < n → ∀ a, X.table a n = A.table a n + B.table a n)
    (hm : X.table false r + A.table true r - A.table false r ∈ K.positive r) :
    ∃ (Y Z : Cell K) (hyz : Y.face true r = Z.face false r),
      comp Y Z r hyz = X ∧
      (∀ n, r < n → ∀ a, Y.table a n = A.table a n) ∧
      (∀ n, r < n → ∀ a, Z.table a n = B.table a n) := by
  have hm' := replacement_middle_eq X A B r (he (r+1) (Nat.lt_succ_self r) false)
  have hA : ∀ a, X.table false r + A.table a r - A.table false r ∈ K.positive r := by
    intro a
    cases a
    · simpa only [add_sub_cancel_right] using X.positive false r
    · exact hm
  have hB : ∀ a, X.table true r + B.table a r - B.table true r ∈ K.positive r := by
    intro a
    cases a
    · rw [← hm']
      exact hm
    · simpa only [add_sub_cancel_right] using X.positive true r
  let Y := replacement X A r false hA
  let Z := replacement X B r true hB
  have hyz : Y.face true r = Z.face false r := by
    apply Cell.ext
    funext a n
    change cutTable Y true r a n = cutTable Z false r a n
    unfold cutTable
    split_ifs with hn heq
    · change replacementTable X A r false a n = replacementTable X B r true a n
      simp only [replacementTable, hn, ite_true]
    · subst n
      simpa only [Y, Z, replacement, replacementTable, Nat.lt_irrefl,
        ite_false, ite_true] using hm'
    · rfl
  refine ⟨Y, Z, hyz, ?_, ?_, ?_⟩
  · apply Cell.ext
    funext a n
    change pasteTable Y Z r a n = X.table a n
    unfold pasteTable
    split_ifs with hn heq ha
    · change replacementTable X A r false a n = _
      simp only [replacementTable, hn, ite_true]
    · subst n
      subst a
      simp [Z, replacement, replacementTable]
    · subst n
      have ha' : a = false := by cases a <;> simp_all
      subst a
      simp [Y, replacement, replacementTable]
    · have hrn : r < n := by omega
      change replacementTable X A r false a n + replacementTable X B r true a n = _
      simp only [replacementTable, hn, heq, ite_false]
      exact (he n hrn a).symm
  · intro n hn a
    change replacementTable X A r false a n = _
    simp only [replacementTable, Nat.not_lt.mpr hn.le, Nat.ne_of_gt hn, ite_false]
  · intro n hn a
    change replacementTable X B r true a n = _
    simp only [replacementTable, Nat.not_lt.mpr hn.le, Nat.ne_of_gt hn, ite_false]

end Thomason.Construction.DirectedComplex.Cell

end

section

/-! # Uniqueness of factors with prescribed upper tables

This is the binary form of Steiner 2004, Proposition 5.8. It is a direct
calculation on cell tables which supplies free-gluing coherence.
-/

namespace Thomason.Construction.DirectedComplex.Cell

universe u

variable {K : DirectedComplex.{u}}

/-- Two r-compositions with the same total and the same upper left factor
have identical factors, including all lower boundary data. -/
theorem factors_unique_of_above (Y Z Y' Z' : Cell K) (r : ℕ)
    (hyz : Y.face true r = Z.face false r)
    (hyz' : Y'.face true r = Z'.face false r)
    (he : comp Y Z r hyz = comp Y' Z' r hyz')
    (hupper : ∀ n, r < n → ∀ side, Y.table side n = Y'.table side n) :
    Y = Y' ∧ Z = Z' := by
  have hlow (n : ℕ) (hn : n < r) (side : Bool) : Y.table side n = Y'.table side n := by
    have hh := congrArg (fun X : Cell K => X.table side n) he
    simpa only [comp_table, pasteTable, hn, ite_true] using hh
  have hfalse : Y.table false r = Y'.table false r := by
    have hh := congrArg (fun X : Cell K => X.table false r) he
    simpa only [comp_table, pasteTable, Nat.lt_irrefl, ite_false, ite_true,
      Bool.false_eq_true] using hh
  have htrue : Y.table true r = Y'.table true r := by
    have hh := congrArg (K.differential r) (hupper (r+1) (by omega) false)
    rw [Y.boundary, Y'.boundary, hfalse] at hh
    simpa only [sub_add_cancel] using congrArg (fun z => z + Y'.table false r) hh
  have hY : Y = Y' := by
    apply Cell.ext
    funext side n
    rcases lt_trichotomy n r with hn | rfl | hn
    · exact hlow n hn side
    · cases side <;> assumption
    · exact hupper n hn side
  refine ⟨hY, ?_⟩
  apply Cell.ext
  funext side n
  rcases lt_trichotomy n r with hn | rfl | hn
  · exact (matching_below hyz side hn).symm.trans
      ((hlow n hn side).trans (matching_below hyz' side hn))
  · cases side with
    | false => exact (matching_top hyz).symm.trans (htrue.trans (matching_top hyz'))
    | true =>
      have hh := congrArg (fun X : Cell K => X.table true n) he
      simpa only [comp_table, pasteTable, Nat.lt_irrefl, ite_false, ite_true] using hh
  · have hh := congrArg (fun X : Cell K => X.table side n) he
    simp only [comp_table, pasteTable, Nat.not_lt.mpr hn.le, Nat.ne_of_gt hn, ite_false] at hh
    rw [hupper n hn side] at hh
    exact add_left_cancel hh

end Thomason.Construction.DirectedComplex.Cell

end

section

/-! # Uniqueness of an entire ordered string of positive-table factors

The binary reconstruction gives Steiner's Proposition 5.8 for any finite
nonempty string, once corresponding factors have the same upper tables.
-/

namespace Thomason.Construction.DirectedComplex.Cell

open StrictOmegaCategory

universe u

variable {K : DirectedComplex.{u}} {r : ℕ}

/-- Above the composition degree, the table of a string is the sum of its
factor tables. -/
theorem compositeList_table {xs : List (Cell K)} {x : Cell K}
    (h : CompositeList K.realization r xs x) (n : ℕ) (hn : r < n) (side : Bool) :
    x.table side n = (xs.map (fun y => y.table side n)).sum := by
  refine CompositeList.rec
    (motive := fun (xs : List K.realization) (x : K.realization) _ =>
      x.table side n = (xs.map (fun y => y.table side n)).sum) ?_ ?_ h
  · intro x
    simp only [List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
  · intro x xs y hy hxy ih
    dsimp only [DirectedComplex.realization] at x xs y hxy ih ⊢
    simp only [comp_table, pasteTable, Nat.not_lt.mpr hn.le,
      Nat.ne_of_gt hn, ite_false, List.map_cons, List.sum_cons]
    rw [ih]

theorem compositeList_factors_unique {xs ys : List (Cell K)} {x y : Cell K}
    (hx : CompositeList K.realization r xs x)
    (hy : CompositeList K.realization r ys y) (hxy : x = y)
    (hupper : List.Forall₂ (fun A D : Cell K =>
      ∀ n, r < n → ∀ side, A.table side n = D.table side n) xs ys) : xs = ys := by
  refine CompositeList.rec
    (motive := fun (xs : List K.realization) (x : K.realization) _ =>
      ∀ (ys : List K.realization) (y : K.realization),
        CompositeList K.realization r ys y → x = y →
        List.Forall₂ (fun A D : Cell K =>
          ∀ n, r < n → ∀ side, A.table side n = D.table side n) xs ys → xs = ys)
    ?_ ?_ hx ys y hy hxy hupper
  · intro x ys y hy hxy hupper
    cases hy with
    | singleton y => exact congrArg (fun z => [z]) hxy
    | @cons y ys z hz hyz =>
      cases hupper with
      | cons hhead htail =>
        cases htail
        exact (hz.nonempty rfl).elim
  · intro x xs z hz hxz ih ys y hy hxy hupper
    cases hy with
    | singleton y =>
      cases hupper with
      | cons hhead htail =>
        cases htail
        exact (hz.nonempty rfl).elim
    | @cons y ys w hw hyw =>
      cases hupper with
      | cons hhead htail =>
        have he := factors_unique_of_above x z y w r hxz hyw hxy hhead
        exact congrArg₂ List.cons he.1 (ih ys w hw he.2 htail)

end Thomason.Construction.DirectedComplex.Cell

end

section

/-!
# The normalized directed simplex complex

The degree-p group is the free abelian group on strictly increasing
(p+1)-tuples of vertices. The differential is alternating deletion and the
positive cone consists of nonnegative coefficients. These normalized chains define the orientals. The differential identity
is described in Steiner (2007), Section 3, the oriental identification in
Theorem 3.2, and the cosimplicial action in Section 4.
-/

namespace Thomason.Construction.SimplexComplex

open scoped BigOperators

abbrev Basis (m p : ℕ) := Fin (p + 1) ↪o Fin (m + 1)
abbrev Chains (m p : ℕ) := Basis m p →₀ ℤ

def deleteVertex {m p : ℕ} (s : Basis m (p + 1)) (i : Fin (p + 2)) : Basis m p :=
  (Fin.succAboveOrderEmb i).trans s

noncomputable def differentialBasis (m p : ℕ) (s : Basis m (p + 1)) : Chains m p :=
  ∑ i : Fin (p + 2), Finsupp.single (deleteVertex s i) ((-1 : ℤ) ^ (i : ℕ))

noncomputable def differential (m p : ℕ) : Chains m (p + 1) →ₗ[ℤ] Chains m p :=
  Finsupp.linearCombination ℤ (differentialBasis m p)

noncomputable def augmentation (m : ℕ) : Chains m 0 →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ => 1)

@[simp]
theorem augmentation_single (m : ℕ) (s : Basis m 0) (z : ℤ) :
    augmentation m (Finsupp.single s z) = z := by
  simp [augmentation]

@[simp]
theorem differential_single (m p : ℕ) (s : Basis m (p + 1)) (z : ℤ) :
    differential m p (Finsupp.single s z) = z • differentialBasis m p s := by
  simp [differential]

theorem augmentation_differentialBasis (m : ℕ) (s : Basis m 1) :
    augmentation m (differentialBasis m 0 s) = 0 := by
  simp [differentialBasis, Fin.sum_univ_succ]

theorem augmentation_differential (m : ℕ) (x : Chains m 1) :
    augmentation m (differential m 0 x) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single s z => simp [augmentation_differentialBasis]

def positive (m p : ℕ) : AddSubmonoid (Chains m p) where
  carrier := {x | ∀ s, 0 ≤ x s}
  zero_mem' := fun _ => le_rfl
  add_mem' hx hy s := add_nonneg (hx s) (hy s)

/-- The usual differential identity on these concrete normalized chains. -/
def BoundarySquared (m : ℕ) : Prop :=
  ∀ (p : ℕ) (x : Chains m (p + 2)), differential m p (differential m (p + 1) x) = 0

/-- The augmented directed simplex complex with its differential identity. -/
noncomputable abbrev directedComplex (m : ℕ) (hsq : BoundarySquared m) : DirectedComplex where
  group p := AddCommGrpCat.of (Chains m p)
  differential p := (differential m p).toAddMonoidHom
  differential_squared := hsq
  augmentation := (augmentation m).toAddMonoidHom
  augmentation_differential := augmentation_differential m
  positive := positive m

/-- The m-th oriental is the strict realization of the normalized directed
simplex. -/
noncomputable def oriental (m : ℕ) (hsq : BoundarySquared m) : StrictOmegaCategory :=
  (directedComplex m hsq).realization

/-- A monotone vertex map takes a nondegenerate simplex to its image if that
image is nondegenerate, and to zero otherwise. -/
noncomputable def mapBasis {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (p : ℕ) (s : Basis m p) : Chains n p := by
  classical
  exact if h : StrictMono (fun i => f (s i)) then
    Finsupp.single (OrderEmbedding.ofStrictMono (fun i => f (s i)) h) 1 else 0

noncomputable def mapChains {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) (p : ℕ) :
    Chains m p →ₗ[ℤ] Chains n p :=
  Finsupp.linearCombination ℤ (mapBasis f p)

@[simp]
theorem mapChains_single {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) (p : ℕ)
    (s : Basis m p) (z : ℤ) : mapChains f p (Finsupp.single s z) = z • mapBasis f p s := by
  simp [mapChains]

theorem mapBasis_nonneg {m n p : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (s : Basis m p) (t : Basis n p) : 0 ≤ mapBasis f p s t := by
  classical
  unfold mapBasis
  split_ifs
  · simp only [Finsupp.single_apply]
    split_ifs <;> norm_num
  · simp

theorem mapChains_positive {m n p : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    {x : Chains m p} (hx : x ∈ positive m p) : mapChains f p x ∈ positive n p := by
  classical
  intro t
  simp only [mapChains, Finsupp.linearCombination_apply, Finsupp.sum,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact Finset.sum_nonneg fun s _ => mul_nonneg (hx s) (mapBasis_nonneg f s t)

theorem augmentation_mapBasis {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (s : Basis m 0) : augmentation n (mapBasis f 0 s) = 1 := by
  have h : StrictMono (fun i => f (s i)) := fun i j hij => by
    have : i = j := Fin.ext (by omega)
    subst j
    exact False.elim (lt_irrefl _ hij)
  simp [mapBasis, h]

theorem augmentation_mapChains {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (x : Chains m 0) : augmentation n (mapChains f 0 x) = augmentation m x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single s z => simp [augmentation_mapBasis]

@[simp]
theorem mapBasis_id {m p : ℕ} (s : Basis m p) :
    mapBasis (OrderHom.id : Fin (m + 1) →o Fin (m + 1)) p s = Finsupp.single s 1 := by
  classical
  have h : StrictMono (fun i => (OrderHom.id : Fin (m + 1) →o Fin (m + 1)) (s i)) :=
    s.strictMono
  rw [mapBasis, dite_eq_left h]
  rfl

@[simp]
theorem mapChains_id {m p : ℕ} (x : Chains m p) :
    mapChains (OrderHom.id : Fin (m + 1) →o Fin (m + 1)) p x = x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single s z => simp

theorem mapBasis_comp {m n k p : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (n + 1) →o Fin (k + 1)) (s : Basis m p) :
    mapChains g p (mapBasis f p s) = mapBasis (g.comp f) p s := by
  classical
  by_cases hf : StrictMono (fun i => f (s i))
  · let t : Basis n p := OrderEmbedding.ofStrictMono (fun i => f (s i)) hf
    have ht : mapBasis f p s = Finsupp.single t 1 := dite_eq_left hf
    rw [ht, mapChains_single, one_smul]
    by_cases hg : StrictMono (fun i => g (t i))
    · have hgf : StrictMono (fun i => (g.comp f) (s i)) := hg
      simp only [mapBasis, dite_eq_left hg, dite_eq_left hgf]
      rfl
    · have hgf : ¬StrictMono (fun i => (g.comp f) (s i)) := hg
      simp only [mapBasis, dite_eq_right hg, dite_eq_right hgf]
  · have hgf : ¬StrictMono (fun i => (g.comp f) (s i)) := by
      intro h
      apply hf
      intro i j hij
      exact lt_of_not_ge fun hle => (not_le_of_gt (h hij)) (g.monotone hle)
    simp only [mapBasis, dite_eq_right hf, dite_eq_right hgf, map_zero]

theorem mapChains_comp {m n k p : ℕ} (f : Fin (m + 1) →o Fin (n + 1))
    (g : Fin (n + 1) →o Fin (k + 1)) (x : Chains m p) :
    mapChains g p (mapChains f p x) = mapChains (g.comp f) p x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single s z => simp [mapBasis_comp]

/-- The classical naturality identity for alternating normalized chains.
This is the normalized simplex chain-map assertion of Steiner (2007),
Section 4. -/
def BoundaryNaturality {m n : ℕ} (f : Fin (m + 1) →o Fin (n + 1)) : Prop :=
  ∀ (p : ℕ) (x : Chains m (p + 1)),
    mapChains f p (differential m p x) = differential n p (mapChains f (p + 1) x)

noncomputable def directedMap {m n : ℕ} (hm : BoundarySquared m) (hn : BoundarySquared n)
    (f : Fin (m + 1) →o Fin (n + 1)) (hf : BoundaryNaturality f) :
    DirectedComplex.Hom (directedComplex m hm) (directedComplex n hn) where
  app p := (mapChains f p).toAddMonoidHom
  differential := hf
  augmentation := augmentation_mapChains f
  positive _ := mapChains_positive f

end Thomason.Construction.SimplexComplex

end

section

/-! # Square-zero for the explicit normalized simplex differential

The two deletion orders are paired by a fixed-point-free involution on
indices. They give the same remaining simplex and opposite signs. This
discharges the square-zero part of the classical normalized-chain input.
-/

namespace Thomason.Construction.SimplexComplex

open scoped BigOperators

/-- Swap the order of two vertex deletions, accounting for the index shift. -/
def swapDeletion {p : ℕ} (ij : Fin (p + 3) × Fin (p + 2)) :
    Fin (p + 3) × Fin (p + 2) :=
  (ij.1.succAbove ij.2, ij.2.predAbove ij.1)

/-- Swapping the two deleted original vertices twice restores both indices. -/
theorem swapDeletion_involutive {p : ℕ} : Function.Involutive (@swapDeletion p) := by
  rintro ⟨i, j⟩
  exact Prod.ext (Fin.succAbove_succAbove_predAbove i j)
    (Fin.predAbove_predAbove_succAbove i j)

/-- The paired deletion order gives exactly the same basis simplex. -/
theorem deleteVertex_swap {m p : ℕ} (s : Basis m (p + 2))
    (i : Fin (p + 3)) (j : Fin (p + 2)) :
    deleteVertex (deleteVertex s (i.succAbove j)) (j.predAbove i) =
      deleteVertex (deleteVertex s i) j := by
  ext k
  exact congrArg (fun v => (s v).val)
    (Fin.succAbove_succAbove_succAbove_predAbove i j k)

/-- Exactly one index changes by one when the order of deletion is exchanged. -/
theorem deletion_sign {p : ℕ} (i : Fin (p + 3)) (j : Fin (p + 2)) :
    (-1 : ℤ) ^ ((i.succAbove j).val + (j.predAbove i).val) =
      -((-1 : ℤ) ^ (i.val + j.val)) := by
  by_cases hij : j.castSucc < i
  · have hs : (i.succAbove j).val + (j.predAbove i).val + 1 = i.val + j.val := by
      rw [Fin.succAbove_of_castSucc_lt _ _ hij, Fin.predAbove_of_castSucc_lt _ _ hij]
      simp only [Fin.val_castSucc, Fin.val_pred]
      omega
    have he := congrArg (fun k => (-1 : ℤ) ^ k) hs
    rw [pow_succ, mul_neg_one] at he
    exact (neg_eq_iff_eq_neg).mp he
  · have hle : i ≤ j.castSucc := le_of_not_gt hij
    have hs : (i.succAbove j).val + (j.predAbove i).val = i.val + j.val + 1 := by
      rw [Fin.succAbove_of_le_castSucc _ _ hle, Fin.predAbove_of_le_castSucc _ _ hle]
      simp only [Fin.val_succ, Fin.coe_castPred]
      omega
    rw [hs, pow_succ, mul_neg_one]

/-- Alternating double deletion vanishes on each nondegenerate simplex. -/
theorem differential_squared_basis {m p : ℕ} (s : Basis m (p + 2)) :
    differential m p (differentialBasis m (p + 1) s) = 0 := by
  classical
  let term (ij : Fin (p + 3) × Fin (p + 2)) : Chains m p :=
    ((-1 : ℤ) ^ (ij.1.val + ij.2.val)) •
      Finsupp.single (deleteVertex (deleteVertex s ij.1) ij.2) 1
  have hsum : (∑ ij, term ij) = 0 := by
    apply Finset.sum_ninvolution swapDeletion
    · rintro ⟨i, j⟩
      dsimp [term, swapDeletion]
      rw [deleteVertex_swap, deletion_sign, neg_smul]
      exact add_neg_cancel _
    · rintro ⟨i, j⟩ _ he
      have hi := congrArg Prod.fst he
      exact Fin.succAbove_ne i j hi
    · intro ij
      exact Finset.mem_univ _
    · exact swapDeletion_involutive
  rw [differentialBasis, map_sum]
  simp_rw [differential_single, differentialBasis, Finset.smul_sum, Finsupp.smul_single,
    smul_eq_mul, ← pow_add]
  simpa only [Fintype.sum_prod_type, term, Finsupp.smul_single, smul_eq_mul, mul_one]
    using hsum

/-- The concrete normalized differential squares to zero, without hypotheses. -/
theorem boundarySquared (m : ℕ) : BoundarySquared m := by
  intro p x
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single s z => simp [differential_squared_basis]

end Thomason.Construction.SimplexComplex

end

section

/-! # Initial support of positive normalized simplex chains

An extremal first vertex detects a nonzero boundary of any positive chain
that leaves an initial segment, detecting initial-face support without
a composition-generation hypothesis.
-/

namespace Thomason.Construction.SimplexComplex

open scoped BigOperators

/-- Deleting a non-first vertex leaves the first vertex unchanged. -/
theorem deleteVertex_first_of_ne_zero {m p : ℕ} (s : Basis m (p + 1))
    (i : Fin (p + 2)) (hi : i ≠ 0) : deleteVertex s i 0 = s 0 := by
  change s (i.succAbove 0) = s 0
  rw [Fin.succAbove_ne_zero_zero hi]

/-- No vertex of a face lies above the original final vertex. -/
theorem deleteVertex_last_le {m p : ℕ} (s : Basis m (p + 1)) (i : Fin (p + 2)) :
    deleteVertex s i (Fin.last p) ≤ s (Fin.last (p + 1)) :=
  s.monotone (Fin.le_last _)

/-- At the face obtained by deleting the first vertex of b, only the first
face of a simplex starting no later than b can contribute. -/
theorem differentialBasis_at_first_face {m p : ℕ} (s b : Basis m (p + 1))
    (hs : s 0 ≤ b 0) :
    differentialBasis m p s (deleteVertex b 0) =
      Finsupp.single (deleteVertex s 0) (1 : ℤ) (deleteVertex b 0) := by
  classical
  unfold differentialBasis
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single 0]
  · simp only [Fin.val_zero, pow_zero]
  · intro i _ hi
    have hne : deleteVertex s i ≠ deleteVertex b 0 := by
      intro he
      have he0 := congrArg (fun t : Basis m p => t 0) he
      rw [deleteVertex_first_of_ne_zero s i hi] at he0
      have hb : b 0 < deleteVertex b 0 0 :=
        b.strictMono (Fin.succ_pos (0 : Fin (p+1)))
      exact (not_lt_of_ge hs) (hb.trans_eq he0.symm)
    exact Finsupp.single_eq_of_ne hne.symm
  · intro h
    exact False.elim (h (Finset.mem_univ _))

/-- A face of a simplex lying below q also lies below q. -/
theorem differentialBasis_zero_above {m p : ℕ} (s : Basis m (p + 1))
    (t : Basis m p) (q : Fin (m + 1))
    (hs : s (Fin.last (p+1)) ≤ q) (ht : q < t (Fin.last p)) :
    differentialBasis m p s t = 0 := by
  classical
  unfold differentialBasis
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply Finsupp.single_eq_of_ne
  intro he
  have hl := deleteVertex_last_le s i
  rw [← he] at hl
  exact (not_le_of_gt ht) (hl.trans hs)

/-- Support in an initial segment is detected by the differential on positive
chains of positive degree. -/
theorem positive_support_below_of_boundary {m p : ℕ} (q : Fin (m + 1))
    (c : Chains m (p + 1)) (hc : c ∈ positive m (p + 1))
    (hd : ∀ t : Basis m p, q < t (Fin.last p) → differential m p c t = 0) :
    ∀ b : Basis m (p + 1), q < b (Fin.last (p + 1)) → c b = 0 := by
  classical
  intro b hb
  by_contra hcb
  let S := c.support.filter (fun s => q < s (Fin.last (p+1)))
  have hS : S.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hcb, hb⟩⟩
  obtain ⟨a, ha, hmax⟩ := S.exists_max_image (fun s => s 0) hS
  have hac : a ∈ c.support := (Finset.mem_filter.mp ha).1
  have haq : q < a (Fin.last (p+1)) := (Finset.mem_filter.mp ha).2
  let t := deleteVertex a 0
  have hat : q < t (Fin.last p) := haq
  have hnonneg (s : Basis m (p+1)) (hs : s ∈ c.support) :
      0 ≤ differentialBasis m p s t := by
    by_cases hsq : q < s (Fin.last (p+1))
    · have hs0 : s 0 ≤ a 0 := hmax s (Finset.mem_filter.mpr ⟨hs, hsq⟩)
      rw [differentialBasis_at_first_face s a hs0, Finsupp.single_apply]
      split_ifs <;> omega
    · rw [differentialBasis_zero_above s t q (le_of_not_gt hsq) hat]
  have heval : differential m p c t =
      ∑ s ∈ c.support, c s * differentialBasis m p s t := by
    simp only [differential, Finsupp.linearCombination_apply, Finsupp.sum,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  have hsum : c a * differentialBasis m p a t ≤
      ∑ s ∈ c.support, c s * differentialBasis m p s t :=
    Finset.single_le_sum (fun s hs => mul_nonneg (hc s) (hnonneg s hs)) hac
  have hapos : 0 < c a := lt_of_le_of_ne (hc a) (Ne.symm (Finsupp.mem_support_iff.mp hac))
  have hself : differentialBasis m p a t = 1 := by
    rw [differentialBasis_at_first_face a a le_rfl, Finsupp.single_eq_same]
  rw [hself, mul_one, ← heval, hd t hat] at hsum
  exact (not_le_of_gt hapos) hsum

end Thomason.Construction.SimplexComplex

end

section

/-! # Final support of positive simplex chains

The last face has a dimension-dependent sign. Multiplying the boundary
coefficient by this sign makes an extremal last vertex detect every
positive chain leaving a final segment. This is the cosieve counterpart
of the checked initial-support argument.
-/

namespace Thomason.Construction.SimplexComplex

open scoped BigOperators

/-- Deleting a non-last vertex leaves the last vertex unchanged. -/
theorem deleteVertex_last_of_ne_last {m p : ℕ} (s : Basis m (p + 1))
    (i : Fin (p + 2)) (hi : i ≠ Fin.last (p + 1)) :
    deleteVertex s i (Fin.last p) = s (Fin.last (p + 1)) := by
  change s (i.succAbove (Fin.last p)) = _
  rw [Fin.succAbove_ne_last_last hi]

theorem deleteVertex_first_ge {m p : ℕ} (s : Basis m (p + 1)) (i : Fin (p + 2)) :
    s 0 ≤ deleteVertex s i 0 := s.monotone (Fin.zero_le _)

/-- At an extremal last face, all other face coefficients vanish. -/
theorem differentialBasis_at_last_face {m p : ℕ} (s b : Basis m (p + 1))
    (hs : b (Fin.last (p + 1)) ≤ s (Fin.last (p + 1))) :
    differentialBasis m p s (deleteVertex b (Fin.last (p + 1))) =
      Finsupp.single (deleteVertex s (Fin.last (p + 1))) ((-1 : ℤ) ^ (p + 1))
        (deleteVertex b (Fin.last (p + 1))) := by
  classical
  unfold differentialBasis
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single (Fin.last (p + 1))]
  · rfl
  · intro i _ hi
    have hne : deleteVertex s i ≠ deleteVertex b (Fin.last (p + 1)) := by
      intro he
      have he0 := congrArg (fun t : Basis m p => t (Fin.last p)) he
      rw [deleteVertex_last_of_ne_last s i hi] at he0
      have hb : deleteVertex b (Fin.last (p + 1)) (Fin.last p) < b (Fin.last (p + 1)) := by
        change b ((Fin.last (p + 1)).succAbove (Fin.last p)) < _
        rw [Fin.succAbove_last]
        exact b.strictMono (Fin.castSucc_lt_last _)
      exact (not_lt_of_ge hs) (he0 ▸ hb)
    exact Finsupp.single_eq_of_ne hne.symm
  · intro h
    exact False.elim (h (Finset.mem_univ _))

/-- A simplex in a final segment has no boundary below the segment. -/
theorem differentialBasis_zero_below {m p : ℕ} (s : Basis m (p + 1))
    (t : Basis m p) (q : Fin (m + 1)) (hs : q ≤ s 0) (ht : t 0 < q) :
    differentialBasis m p s t = 0 := by
  classical
  unfold differentialBasis
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply Finsupp.single_eq_of_ne
  intro he
  have hl := deleteVertex_first_ge s i
  rw [← he] at hl
  exact (not_le_of_gt ht) (hs.trans hl)

private theorem sign_square (p : ℕ) : ((-1 : ℤ) ^ p) * ((-1 : ℤ) ^ p) = 1 := by
  rw [← mul_pow]
  simp

/-- The boundary detects final support of every positive chain. -/
theorem positive_support_above_of_boundary {m p : ℕ} (q : Fin (m + 1))
    (c : Chains m (p + 1)) (hc : c ∈ positive m (p + 1))
    (hd : ∀ t : Basis m p, t 0 < q → differential m p c t = 0) :
    ∀ b : Basis m (p + 1), b 0 < q → c b = 0 := by
  classical
  intro b hb
  by_contra hcb
  let S := c.support.filter (fun s => s 0 < q)
  have hS : S.Nonempty := ⟨b, Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hcb, hb⟩⟩
  obtain ⟨a, ha, hmin⟩ := S.exists_min_image (fun s => s (Fin.last (p + 1))) hS
  have hac : a ∈ c.support := (Finset.mem_filter.mp ha).1
  have haq : a 0 < q := (Finset.mem_filter.mp ha).2
  let t := deleteVertex a (Fin.last (p + 1))
  have hat : t 0 < q := by
    change a ((Fin.last (p + 1)).succAbove 0) < q
    rw [Fin.succAbove_last]
    exact haq
  let σ : ℤ := (-1) ^ (p + 1)
  have hnonneg (s : Basis m (p + 1)) (hs : s ∈ c.support) :
      0 ≤ σ * differentialBasis m p s t := by
    by_cases hsq : s 0 < q
    · have hslast : a (Fin.last (p + 1)) ≤ s (Fin.last (p + 1)) :=
        hmin s (Finset.mem_filter.mpr ⟨hs, hsq⟩)
      rw [differentialBasis_at_last_face s a hslast, Finsupp.single_apply]
      split_ifs
      · exact (sign_square (p + 1)).symm ▸ (by norm_num : (0 : ℤ) ≤ 1)
      · simp
    · rw [differentialBasis_zero_below s t q (le_of_not_gt hsq) hat, mul_zero]
  have heval : σ * differential m p c t =
      ∑ s ∈ c.support, c s * (σ * differentialBasis m p s t) := by
    simp only [differential, Finsupp.linearCombination_apply, Finsupp.sum,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hsum : c a * (σ * differentialBasis m p a t) ≤
      ∑ s ∈ c.support, c s * (σ * differentialBasis m p s t) :=
    Finset.single_le_sum (fun s hs => mul_nonneg (hc s) (hnonneg s hs)) hac
  have hapos : 0 < c a := lt_of_le_of_ne (hc a) (Ne.symm (Finsupp.mem_support_iff.mp hac))
  have hself : σ * differentialBasis m p a t = 1 := by
    rw [differentialBasis_at_last_face a a le_rfl, Finsupp.single_eq_same]
    exact sign_square (p + 1)
  rw [hself, mul_one, ← heval, hd t hat, mul_zero] at hsum
  exact (not_le_of_gt hapos) hsum

end Thomason.Construction.SimplexComplex

end

end OAI
