import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Tactic

namespace OAI

section

/-!
# Augmented directed complexes and their globular cells

An augmented directed complex consists of chain groups, differentials, an
augmentation and positive submonoids. A globular cell is a
finite table of positive chains, with the boundary and augmentation equations
in Steiner's construction `nu`. Its faces are truncations of this table.
-/

namespace Thomason.Construction

universe u

structure DirectedComplex where
  group : ℕ → AddCommGrpCat.{u}
  differential (n : ℕ) : group (n + 1) →+ group n
  differential_squared (n : ℕ) (x : group (n + 2)) :
    differential n (differential (n + 1) x) = 0
  augmentation : group 0 →+ ℤ
  augmentation_differential (x : group 1) : augmentation (differential 0 x) = 0
  positive (n : ℕ) : AddSubmonoid (group n)

namespace DirectedComplex

/-- A chain map preserving the augmentation and positive submonoids. -/
structure Hom (K L : DirectedComplex.{u}) where
  app (n : ℕ) : K.group n →+ L.group n
  differential (n : ℕ) (x : K.group (n + 1)) :
    app n (K.differential n x) = L.differential n (app (n + 1) x)
  augmentation (x : K.group 0) : L.augmentation (app 0 x) = K.augmentation x
  positive (n : ℕ) {x : K.group n} : x ∈ K.positive n → app n x ∈ L.positive n

/-- The finite positive chain table defining a cell of `nu K`. -/
@[ext]
structure Cell (K : DirectedComplex.{u}) where
  table (a : Bool) (n : ℕ) : K.group n
  positive (a : Bool) (n : ℕ) : table a n ∈ K.positive n
  augmentation (a : Bool) : K.augmentation (table a 0) = 1
  boundary (a : Bool) (n : ℕ) :
    K.differential n (table a (n + 1)) = table true n - table false n
  finite_support : ∃ N, ∀ n, N < n → ∀ a, table a n = 0

namespace Cell

variable {K L M : DirectedComplex.{u}}

/-- Applying a positive chain map in every degree preserves the full table
equations, including the boundary data below any vanishing top chain. -/
def map (f : Hom K L) (x : Cell K) : Cell L where
  table a n := f.app n (x.table a n)
  positive a n := f.positive n (x.positive a n)
  augmentation a := (f.augmentation _).trans (x.augmentation a)
  boundary a n := by
    rw [← f.differential, x.boundary, map_sub]
  finite_support := by
    obtain ⟨N, hN⟩ := x.finite_support
    exact ⟨N, fun n hn a => by rw [hN n hn a, map_zero]⟩

@[simp]
theorem map_table (f : Hom K L) (x : Cell K) (a : Bool) (n : ℕ) :
    (map f x).table a n = f.app n (x.table a n) := rfl

/-- Truncate a table at degree `n`, retaining the chosen boundary twice in
that degree. The lower-dimensional entries remain unchanged. -/
def cutTable (x : Cell K) (a : Bool) (n : ℕ) (b : Bool) (m : ℕ) : K.group m :=
  if m < n then x.table b m else if m = n then x.table a m else 0

def face (x : Cell K) (a : Bool) (n : ℕ) : Cell K where
  table := x.cutTable a n
  positive b m := by
    unfold cutTable
    split_ifs
    · exact x.positive b m
    · exact x.positive a m
    · exact (K.positive m).zero_mem
  augmentation b := by
    by_cases hn : n = 0
    · subst n
      simpa only [cutTable, Nat.lt_irrefl, ite_false, ite_true] using x.augmentation a
    · have hn' : 0 < n := Nat.pos_of_ne_zero hn
      simpa only [cutTable, hn', ite_true] using x.augmentation b
  boundary b m := by
    by_cases h : m + 1 < n
    · have hm : m < n := by omega
      simp only [cutTable, h, hm, ite_true, x.boundary]
    · by_cases he : m + 1 = n
      · have hm : m < n := by omega
        subst n
        simp only [cutTable, Nat.lt_irrefl, Nat.lt_succ_self, ite_false,
          ite_true, x.boundary]
      · have hm : ¬m < n := by omega
        by_cases hmn : m = n
        · subst n
          simp [cutTable]
        · simp only [cutTable, h, he, hm, hmn, ite_false, map_zero, sub_self]
  finite_support := ⟨n, fun m hm a => by
    simp only [cutTable, Nat.not_lt.mpr (Nat.le_of_lt hm),
      Nat.ne_of_gt hm, ite_false]⟩

@[simp]
theorem face_table (x : Cell K) (a : Bool) (n : ℕ) (b : Bool) (m : ℕ) :
    (x.face a n).table b m = x.cutTable a n b m := rfl

/-- Positive chain maps preserve globular source and target truncation. -/
theorem map_face (f : Hom K L) (x : Cell K) (a : Bool) (n : ℕ) :
    map f (x.face a n) = (map f x).face a n := by
  ext b m
  simp only [map_table, face_table, cutTable]
  split_ifs <;> simp only [map_zero]

/-- The face operations satisfy the strict globular identities. -/
theorem face_face (x : Cell K) (a b : Bool) (m n : ℕ) :
    (x.face b n).face a m = if m < n then x.face a m else x.face b n := by
  ext c k
  by_cases hmn : m < n
  · rw [ite_eq_left hmn]
    simp only [face_table, cutTable]
    split_ifs <;> (try rfl)
    all_goals omega
  · rw [ite_eq_right hmn]
    simp only [face_table, cutTable]
    split_ifs <;> (try rfl)
    all_goals omega

theorem matching_top {x y : Cell K} {n : ℕ} (h : x.face true n = y.face false n) :
    x.table true n = y.table false n := by
  have h' := congrArg (fun z : Cell K => z.table false n) h
  simpa only [face_table, cutTable, Nat.lt_irrefl, ite_false, ite_true] using h'

theorem matching_below {x y : Cell K} {n : ℕ} (h : x.face true n = y.face false n)
    (a : Bool) {m : ℕ} (hm : m < n) : x.table a m = y.table a m := by
  have h' := congrArg (fun z : Cell K => z.table a m) h
  simpa only [face_table, cutTable, hm, ite_true] using h'

/-- The table for composition along dimension `n`: retain common lower data,
take the exterior boundaries at `n`, and add the higher chains. -/
def pasteTable (x y : Cell K) (n : ℕ) (a : Bool) (m : ℕ) : K.group m :=
  if m < n then x.table a m
  else if m = n then if a then y.table true m else x.table false m
  else x.table a m + y.table a m

def comp (x y : Cell K) (n : ℕ) (h : x.face true n = y.face false n) : Cell K where
  table := pasteTable x y n
  positive a m := by
    unfold pasteTable
    split_ifs
    · exact x.positive a m
    · exact y.positive true m
    · exact x.positive false m
    · exact (K.positive m).add_mem (x.positive a m) (y.positive a m)
  augmentation a := by
    by_cases hn : n = 0
    · subst n
      cases a <;> simp only [pasteTable, Nat.lt_irrefl, ite_false, ite_true,
        Bool.false_eq_true, x.augmentation, y.augmentation]
    · have hn' : 0 < n := Nat.pos_of_ne_zero hn
      simp only [pasteTable, hn', ite_true, x.augmentation]
  boundary a m := by
    by_cases hm : m + 1 < n
    · have hm' : m < n := by omega
      simp only [pasteTable, hm, hm', ite_true, x.boundary]
    · by_cases he : m + 1 = n
      · have hm' : m < n := by omega
        subst n
        cases a
        · simp only [pasteTable, Nat.lt_irrefl, Nat.lt_succ_self, ite_false, ite_true,
            Bool.false_eq_true, x.boundary]
        · simp only [pasteTable, Nat.lt_irrefl, Nat.lt_succ_self, ite_false, ite_true,
            y.boundary]
          rw [matching_below h true (Nat.lt_succ_self m),
            matching_below h false (Nat.lt_succ_self m)]
      · have hm' : n ≤ m := by omega
        by_cases hmn : m = n
        · subst n
          simp [pasteTable, x.boundary, y.boundary]
          have ht : x.table true m = y.table false m := matching_top h
          rw [ht]
          abel
        · have hnlt : ¬m < n := by omega
          simp only [pasteTable, hm, he, hnlt, hmn, ite_false, map_add,
            x.boundary, y.boundary]
          abel
  finite_support := by
    obtain ⟨N, hN⟩ := x.finite_support
    obtain ⟨M, hM⟩ := y.finite_support
    refine ⟨max n (max N M), ?_⟩
    intro m hm a
    have hnm : n < m := lt_of_le_of_lt (le_max_left _ _) hm
    have hNm : N < m := lt_of_le_of_lt ((le_max_left N M).trans (le_max_right _ _)) hm
    have hMm : M < m := lt_of_le_of_lt ((le_max_right N M).trans (le_max_right _ _)) hm
    simp only [pasteTable, Nat.not_lt.mpr hnm.le, Nat.ne_of_gt hnm, ite_false,
      hN m hNm a, hM m hMm a, add_zero]

@[simp]
theorem comp_table (x y : Cell K) (n : ℕ) (h) (a : Bool) (m : ℕ) :
    (comp x y n h).table a m = pasteTable x y n a m := rfl

/-- Positive chain maps respect composition of globular
tables. This includes maps sending generators to sums or zero. -/
theorem map_comp (f : Hom K L) (x y : Cell K) (n : ℕ)
    (h : x.face true n = y.face false n)
    (h' : (map f x).face true n = (map f y).face false n) :
    map f (comp x y n h) = comp (map f x) (map f y) n h' := by
  ext a m
  simp only [map_table, comp_table, pasteTable]
  split_ifs <;> simp only [map_add]

end Cell
end DirectedComplex
end Thomason.Construction

end

end OAI
