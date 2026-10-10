import OAI.CategoryTheory.Thomason.Chains.FinalPositiveSimplexSupport
import OAI.CategoryTheory.Thomason.Gray.OrderedAtomGrouping
import OAI.CategoryTheory.Thomason.Strict.StrictCompositeListReplacement
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic

namespace OAI

section

/-! # An upper table determines its finite atom multiset

At the largest degree a top coefficient can only come from that exact
basis atom. Removing one common occurrence and repeating proves uniqueness
of the complete finite multiset. This uses only the triangular top tables,
not the free-gluing theorem under construction.
-/

namespace Thomason.Construction.DirectedComplex.OrderedAtomBasis

variable {K : DirectedComplex.{0}} (B : OrderedAtomBasis K)

theorem atom_coefficient_zero_of_ne (a b : B.AtomIndex) (hb : b.1 ≤ a.1)
    (hne : b ≠ a) : B.coordinates a.1 ((B.atomCell b).table false a.1) a.2 = 0 := by
  classical
  rcases a with ⟨p,a⟩
  rcases b with ⟨q,b⟩
  by_cases hpq : p = q
  · subst q
    have hab : a ≠ b := by
      intro h
      subst b
      exact hne rfl
    exact (congrArg (fun f => f a) (B.atom_top p b false)).trans
      (Finsupp.single_eq_of_ne hab)
  · have hqp : q < p := by change q ≤ p at hb; omega
    change B.coordinates p ((B.atom q b).table false p) a = 0
    rw [B.atom_above q b p hqp false, map_zero, Finsupp.zero_apply]

theorem atomSum_coefficient_pos (as : List B.AtomIndex) (a : B.AtomIndex) (ha : a ∈ as) :
    0 < B.coordinates a.1
      ((Cell.PositiveTable.ofCells (as.map B.atomCell)).table false a.1) a.2 := by
  classical
  have hp := (List.perm_cons_erase ha).map (fun b => (B.atomCell b).table false a.1)
  have he : (Cell.PositiveTable.ofCells (as.map B.atomCell)).table false a.1 =
      (B.atomCell a).table false a.1 +
        (Cell.PositiveTable.ofCells ((as.erase a).map B.atomCell)).table false a.1 := by
    simpa only [Cell.PositiveTable.ofCells_table, List.map_map, Function.comp_def,
      List.map_cons, List.sum_cons]
      using hp.sum_eq
  have hh := congrArg (fun x => B.coordinates a.1 x a.2) he
  have hpos := B.coordinate_nonnegative a.1 _
    ((Cell.PositiveTable.ofCells ((as.erase a).map B.atomCell)).positive false a.1) a.2
  simp only [map_add, Finsupp.add_apply, atomCell, B.atom_top, Finsupp.single_eq_same] at hh
  omega

theorem atom_mem_of_coefficient_ne_zero (as : List B.AtomIndex) (a : B.AtomIndex)
    (hd : ∀ b ∈ as, b.1 ≤ a.1)
    (hc : B.coordinates a.1
      ((Cell.PositiveTable.ofCells (as.map B.atomCell)).table false a.1) a.2 ≠ 0) : a ∈ as := by
  by_contra hn
  apply hc
  apply B.sumCells_coordinate_zero
  intro X hX
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hX
  exact B.atom_coefficient_zero_of_ne a b (hd b hb) (fun he => hn (he ▸ hb))

theorem common_atom_of_upper_sum (r : ℕ) (as bs : List B.AtomIndex)
    (hne : as ++ bs ≠ []) (hd : ∀ a ∈ as ++ bs, r < a.1)
    (he : ∀ n, r < n → ∀ side,
      (Cell.PositiveTable.ofCells (as.map B.atomCell)).table side n =
      (Cell.PositiveTable.ofCells (bs.map B.atomCell)).table side n) :
    ∃ a, a ∈ as ∧ a ∈ bs := by
  let ds := (as ++ bs).map (fun a => a.1)
  have hds : ds ≠ [] := fun h => hne (List.map_eq_nil_iff.mp h)
  obtain ⟨a, ha, ham⟩ := List.mem_map.mp (List.max_mem hds)
  have hmax : ∀ b ∈ as ++ bs, b.1 ≤ a.1 := by
    intro b hb
    have hm := List.le_max_of_mem (List.mem_map.mpr ⟨b, hb, rfl⟩ : b.1 ∈ ds)
    exact hm.trans_eq ham.symm
  have transfer (xs ys : List B.AtomIndex) (ha : a ∈ xs)
      (hys : ∀ b ∈ ys, b.1 ≤ a.1)
      (heq : (Cell.PositiveTable.ofCells (xs.map B.atomCell)).table false a.1 =
        (Cell.PositiveTable.ofCells (ys.map B.atomCell)).table false a.1) : a ∈ ys := by
    apply B.atom_mem_of_coefficient_ne_zero ys a hys
    have hh := B.atomSum_coefficient_pos xs a ha
    rw [heq] at hh
    exact ne_of_gt hh
  rcases List.mem_append.mp ha with has | hbs
  · exact ⟨a, has, transfer as bs has
      (fun b hb => hmax b (List.mem_append_right as hb))
      (he a.1 (hd a (List.mem_append_left bs has)) false)⟩
  · exact ⟨a, transfer bs as hbs
      (fun b hb => hmax b (List.mem_append_left bs hb))
      (he a.1 (hd a (List.mem_append_right as hbs)) false).symm, hbs⟩

theorem upper_sum_perm (r : ℕ) (as bs : List B.AtomIndex)
    (hd : ∀ a ∈ as ++ bs, r < a.1)
    (he : ∀ n, r < n → ∀ side,
      (Cell.PositiveTable.ofCells (as.map B.atomCell)).table side n =
      (Cell.PositiveTable.ofCells (bs.map B.atomCell)).table side n) : as.Perm bs := by
  classical
  suffices aux : ∀ k (as bs : List B.AtomIndex), as.length = k →
      (∀ a ∈ as ++ bs, r < a.1) →
      (∀ n, r < n → ∀ side,
        (Cell.PositiveTable.ofCells (as.map B.atomCell)).table side n =
        (Cell.PositiveTable.ofCells (bs.map B.atomCell)).table side n) → as.Perm bs by
    exact aux as.length as bs rfl hd he
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro as bs hlen hd he
    by_cases hne : as ++ bs = []
    · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hne
      exact List.Perm.refl []
    obtain ⟨a, ha, hb⟩ := B.common_atom_of_upper_sum r as bs hne hd he
    have hsmall : (as.erase a).length < k := by
      have hh : (as.erase a).length + 1 = as.length := by
        simpa only [List.length_cons] using (List.perm_cons_erase ha).length_eq.symm
      omega
    have ht : ∀ n, r < n → ∀ side,
        (Cell.PositiveTable.ofCells ((as.erase a).map B.atomCell)).table side n =
        (Cell.PositiveTable.ofCells ((bs.erase a).map B.atomCell)).table side n := by
      intro n hn side
      have hp := ((List.perm_cons_erase ha).map (fun c => (B.atomCell c).table side n)).sum_eq
      have hq := ((List.perm_cons_erase hb).map (fun c => (B.atomCell c).table side n)).sum_eq
      have hh := he n hn side
      simp only [Cell.PositiveTable.ofCells_table, List.map_map, Function.comp_def] at hh ⊢
      simp only [List.map_cons, List.sum_cons] at hp hq
      rw [hp, hq] at hh
      exact add_left_cancel hh
    have hd' : ∀ c ∈ as.erase a ++ bs.erase a, r < c.1 := by
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hd c (List.mem_append_left bs (List.mem_of_mem_erase hc))
      · exact hd c (List.mem_append_right as (List.mem_of_mem_erase hc))
    have hi := ih (as.erase a).length hsmall (as.erase a) (bs.erase a) rfl hd' ht
    exact (List.perm_cons_erase ha).trans ((hi.cons a).trans (List.perm_cons_erase hb).symm)

end Thomason.Construction.DirectedComplex.OrderedAtomBasis

end

section

/-!
# Tensoring a directed complex on the right with the interval

In degree n, the two endpoint copies of K_n are accompanied (for n > 0)
by K_{n-1} tensored with the oriented interval edge. The differential has
the sign (-1)^(n-1) required for a right tensor factor. This is a concrete
specialization of the chain tensor, not an assumed cylinder functor.
-/

namespace Thomason.Construction.DirectedComplex

universe u

namespace RightCylinder

variable (K : DirectedComplex.{u})

abbrev group : ℕ → AddCommGrpCat.{u}
  | 0 => AddCommGrpCat.of (K.group 0 × K.group 0)
  | n + 1 => AddCommGrpCat.of (K.group (n + 1) × K.group (n + 1) × K.group n)

def differential : (n : ℕ) → group K (n + 1) →+ group K n
  | 0 =>
    { toFun := fun x => (K.differential 0 x.1 - x.2.2, K.differential 0 x.2.1 + x.2.2)
      map_zero' := by ext <;> simp
      map_add' := by intro x y; ext <;> simp <;> abel }
  | n + 1 =>
    { toFun := fun x =>
        (K.differential (n + 1) x.1 - ((-1 : ℤ) ^ (n + 1)) • x.2.2,
         K.differential (n + 1) x.2.1 + ((-1 : ℤ) ^ (n + 1)) • x.2.2,
         K.differential n x.2.2)
      map_zero' := by ext <;> simp
      map_add' := by intro x y; ext <;> simp <;> abel }

theorem differential_squared (n : ℕ) (x : group K (n + 2)) :
    differential K n (differential K (n + 1) x) = 0 := by
  cases n with
  | zero =>
    ext <;> simp [differential, K.differential_squared]
  | succ n =>
    ext <;> simp [differential, K.differential_squared, pow_succ]

def augmentation : group K 0 →+ ℤ where
  toFun x := K.augmentation x.1 + K.augmentation x.2
  map_zero' := by simp
  map_add' := by intros; simp; abel

theorem augmentation_differential (x : group K 1) :
    augmentation K (differential K 0 x) = 0 := by
  simp [augmentation, differential, K.augmentation_differential]

def positive : (n : ℕ) → AddSubmonoid (group K n)
  | 0 => (K.positive 0).prod (K.positive 0)
  | n + 1 => (K.positive (n + 1)).prod ((K.positive (n + 1)).prod (K.positive n))

end RightCylinder

/-- The directed chain tensor K ⊗ M[1], with the interval on the right. -/
abbrev rightCylinder (K : DirectedComplex.{u}) : DirectedComplex.{u} where
  group := RightCylinder.group K
  differential := RightCylinder.differential K
  differential_squared := RightCylinder.differential_squared K
  augmentation := RightCylinder.augmentation K
  augmentation_differential := RightCylinder.augmentation_differential K
  positive := RightCylinder.positive K

namespace RightCylinder

variable (K : DirectedComplex.{u})

def endpointMap (a : Bool) : (n : ℕ) → K.group n →+ (rightCylinder K).group n
  | 0 =>
    { toFun := fun x => if a then (0, x) else (x, 0)
      map_zero' := by cases a <;> simp
      map_add' := by intros; cases a <;> simp }
  | _ + 1 =>
    { toFun := fun x => if a then (0, x, 0) else (x, 0, 0)
      map_zero' := by cases a <;> simp
      map_add' := by intros; cases a <;> simp }

/-- Both inclusions of K into its right chain cylinder are positive chain maps. -/
def endpoint (a : Bool) : Hom K (rightCylinder K) where
  app := endpointMap K a
  differential n x := by
    cases n <;> cases a <;> ext <;> simp [endpointMap, rightCylinder, differential]
  augmentation x := by cases a <;> simp [endpointMap, rightCylinder, augmentation]
  positive n x hx := by
    cases n with
    | zero =>
      cases a with
      | false => exact ⟨hx, (K.positive 0).zero_mem⟩
      | true => exact ⟨(K.positive 0).zero_mem, hx⟩
    | succ n =>
      cases a with
      | false => exact ⟨hx, (K.positive _).zero_mem, (K.positive _).zero_mem⟩
      | true => exact ⟨(K.positive _).zero_mem, hx, (K.positive _).zero_mem⟩

def projectionMap : (n : ℕ) → (rightCylinder K).group n →+ K.group n
  | 0 =>
    { toFun := fun x => x.1 + x.2
      map_zero' := by simp
      map_add' := by intros; simp; abel }
  | _ + 1 =>
    { toFun := fun x => x.1 + x.2.1
      map_zero' := by simp
      map_add' := by intros; simp; abel }

/-- Collapsing the right interval is a positive augmented chain map. -/
def projection : Hom (rightCylinder K) K where
  app := projectionMap K
  differential n x := by
    cases n <;> simp [projectionMap, rightCylinder, differential]
  augmentation x := by simp [projectionMap, rightCylinder, augmentation]
  positive n x hx := by
    cases n with
    | zero => exact (K.positive _).add_mem hx.1 hx.2
    | succ n => exact (K.positive _).add_mem hx.1 hx.2.1

@[simp]
theorem projection_endpoint (a : Bool) (n : ℕ) (x : K.group n) :
    (projection K).app n ((endpoint K a).app n x) = x := by
  cases n <;> cases a <;> simp [projection, projectionMap, endpoint, endpointMap]

/-- The endpoint–projection identity survives strict realization. -/
theorem realization_projection_endpoint (a : Bool) (x : K.realization) :
    (projection K).realization ((endpoint K a).realization x) = x := by
  apply Cell.ext
  funext b n
  exact projection_endpoint K a n (x.table b n)

variable {K} {L : DirectedComplex.{u}}

def mapMap (f : Hom K L) : (n : ℕ) → (rightCylinder K).group n →+
    (rightCylinder L).group n
  | 0 =>
    { toFun := fun x => (f.app 0 x.1, f.app 0 x.2)
      map_zero' := by ext <;> simp
      map_add' := by intros; ext <;> simp }
  | n + 1 =>
    { toFun := fun x => (f.app (n + 1) x.1, f.app (n + 1) x.2.1, f.app n x.2.2)
      map_zero' := by ext <;> simp
      map_add' := by intros; ext <;> simp }

/-- Tensor a positive augmented chain map with the identity of the interval. -/
def map (f : Hom K L) : Hom (rightCylinder K) (rightCylinder L) where
  app := mapMap f
  differential n x := by
    cases n <;> ext <;> simp [mapMap, differential, f.differential]
  augmentation x := by simp [mapMap, augmentation, f.augmentation]
  positive n x hx := by
    cases n with
    | zero => exact ⟨f.positive 0 hx.1, f.positive 0 hx.2⟩
    | succ n => exact ⟨f.positive _ hx.1, f.positive _ hx.2.1, f.positive _ hx.2.2⟩

theorem map_endpoint (f : Hom K L) (a : Bool) (n : ℕ) (x : K.group n) :
    (map f).app n ((endpoint K a).app n x) = (endpoint L a).app n (f.app n x) := by
  cases n <;> cases a <;> simp [map, mapMap, endpoint, endpointMap]

theorem projection_map (f : Hom K L) (n : ℕ) (x : (rightCylinder K).group n) :
    (projection L).app n ((map f).app n x) = f.app n ((projection K).app n x) := by
  cases n <;> simp [map, mapMap, projection, projectionMap]

/-- Naturality of interval collapse holds for all positive chain maps,
including maps which send basis elements to zero or sums. -/
theorem realization_projection_map (f : Hom K L) (x : (rightCylinder K).realization) :
    (projection L).realization ((map f).realization x) =
      f.realization ((projection K).realization x) := by
  apply Cell.ext
  funext a n
  exact projection_map f n (x.table a n)

end RightCylinder
end Thomason.Construction.DirectedComplex

end

section

/-! # The directed contraction of the concrete right chain cylinder

Minimum on the two oriented interval factors gives a positive chain map.
Its two outer endpoints are the zero-endpoint collapse and the identity;
the inner zero endpoint is fixed. All equalities hold before strict
realization, including the signs in every positive degree.
-/

namespace Thomason.Construction.DirectedComplex.RightCylinder

universe u

variable (K : DirectedComplex.{u})

/-- The chain map induced by minimum on the two right interval factors. -/
def minimumMap : (n : ℕ) →
    (rightCylinder (rightCylinder K)).group n →+ (rightCylinder K).group n
  | 0 => {
      toFun := fun x => (x.1.1 + x.1.2 + x.2.1, x.2.2)
      map_zero' := by ext <;> simp
      map_add' := by intros; ext <;> simp; abel }
  | 1 => {
      toFun := fun x => (x.1.1 + x.1.2.1 + x.2.1.1, x.2.1.2.1,
        x.2.1.2.2 + x.2.2.2)
      map_zero' := by ext <;> simp
      map_add' := by intros; ext <;> simp <;> abel }
  | n+2 => {
      toFun := fun x => (x.1.1 + x.1.2.1 + x.2.1.1, x.2.1.2.1,
        x.2.1.2.2 + x.2.2.2.1)
      map_zero' := by ext <;> simp
      map_add' := by intros; ext <;> simp <;> abel }

theorem minimumMap_differential (n : ℕ)
    (x : (rightCylinder (rightCylinder K)).group (n+1)) :
    minimumMap K n ((rightCylinder (rightCylinder K)).differential n x) =
      (rightCylinder K).differential n (minimumMap K (n+1) x) := by
  cases n with
  | zero => ext <;> simp [minimumMap, rightCylinder, differential] <;> abel
  | succ n =>
    cases n with
    | zero => ext <;> simp [minimumMap, rightCylinder, differential] <;> abel
    | succ n => ext <;> simp [minimumMap, rightCylinder, differential, pow_succ] <;> abel

/-- A positive augmented chain contraction, requiring no abstract Gray input. -/
def minimum : Hom (rightCylinder (rightCylinder K)) (rightCylinder K) where
  app := minimumMap K
  differential := minimumMap_differential K
  augmentation x := by
    simp [minimumMap, rightCylinder, augmentation]
    abel
  positive n x hx := by
    cases n with
    | zero => exact ⟨(K.positive 0).add_mem
        ((K.positive 0).add_mem hx.1.1 hx.1.2) hx.2.1, hx.2.2⟩
    | succ n =>
      cases n with
      | zero => exact ⟨(K.positive 1).add_mem
          ((K.positive 1).add_mem hx.1.1 hx.1.2.1) hx.2.1.1,
          hx.2.1.2.1, (K.positive 0).add_mem hx.2.1.2.2 hx.2.2.2⟩
      | succ n => exact ⟨(K.positive (n+2)).add_mem
          ((K.positive (n+2)).add_mem hx.1.1 hx.1.2.1) hx.2.1.1,
          hx.2.1.2.1, (K.positive (n+1)).add_mem hx.2.1.2.2 hx.2.2.2.1⟩

@[simp]
theorem minimum_outer_one (n : ℕ) (x : (rightCylinder K).group n) :
    (minimum K).app n ((endpoint (rightCylinder K) true).app n x) = x := by
  cases n with
  | zero => ext <;> simp [minimum, minimumMap, endpoint, endpointMap]
  | succ n => cases n <;> ext <;> simp [minimum, minimumMap, endpoint, endpointMap]

@[simp]
theorem minimum_outer_zero (n : ℕ) (x : (rightCylinder K).group n) :
    (minimum K).app n ((endpoint (rightCylinder K) false).app n x) =
      (endpoint K false).app n ((projection K).app n x) := by
  cases n with
  | zero => ext <;> simp [minimum, minimumMap, endpoint, endpointMap, projection, projectionMap]
  | succ n => cases n <;> ext <;>
      simp [minimum, minimumMap, endpoint, endpointMap, projection, projectionMap]

@[simp]
theorem minimum_projection (n : ℕ)
    (x : (rightCylinder (rightCylinder K)).group n) :
    (projection K).app n ((minimum K).app n x) =
      (projection K).app n ((projection (rightCylinder K)).app n x) := by
  cases n with
  | zero => simp [minimum, minimumMap, projection, projectionMap]; abel
  | succ n => cases n <;> simp [minimum, minimumMap, projection, projectionMap] <;> abel

@[simp]
theorem minimum_fixed_zero (n : ℕ) (x : (rightCylinder K).group n) :
    (minimum K).app n ((map (endpoint K false)).app n x) =
      (endpoint K false).app n ((projection K).app n x) := by
  cases n with
  | zero => ext <;> simp [minimum, minimumMap, map, mapMap, endpoint, endpointMap,
      projection, projectionMap]
  | succ n => cases n <;> ext <;>
      simp [minimum, minimumMap, map, mapMap, endpoint, endpointMap, projection, projectionMap]

variable {K} {L : DirectedComplex.{u}}

theorem minimum_naturality (f : Hom K L) (n : ℕ)
    (x : (rightCylinder (rightCylinder K)).group n) :
    (map f).app n ((minimum K).app n x) =
      (minimum L).app n ((map (map f)).app n x) := by
  cases n with
  | zero => ext <;> simp [minimum, minimumMap, map, mapMap]
  | succ n => cases n <;> ext <;> simp [minimum, minimumMap, map, mapMap]

/-- Strict realization keeps the contraction's terminal endpoint literally. -/
theorem realization_minimum_outer_one (x : (rightCylinder K).realization) :
    (minimum K).realization ((endpoint (rightCylinder K) true).realization x) = x := by
  apply Cell.ext
  funext a n
  exact minimum_outer_one K n (x.table a n)

/-- Its initial endpoint is the specified zero section after projection. -/
theorem realization_minimum_outer_zero (x : (rightCylinder K).realization) :
    (minimum K).realization ((endpoint (rightCylinder K) false).realization x) =
      (endpoint K false).realization ((projection K).realization x) := by
  apply Cell.ext
  funext a n
  exact minimum_outer_zero K n (x.table a n)

/-- Collapse commutes with the actual directed contraction. -/
theorem realization_minimum_projection
    (x : (rightCylinder (rightCylinder K)).realization) :
    (projection K).realization ((minimum K).realization x) =
      (projection K).realization ((projection (rightCylinder K)).realization x) := by
  apply Cell.ext
  funext a n
  exact minimum_projection K n (x.table a n)

end Thomason.Construction.DirectedComplex.RightCylinder

end

section

/-! # Strict globes for the right interval construction

The free n-globe has its top cell and two boundary cells in every smaller
dimension. Composition is forced by units. This supplies the finite
strict parameters on which the right interval tensor must be constructed.
-/

namespace Thomason.Construction.StrictOmegaCategory.Globe

inductive Cell (n : ℕ) where
  | top
  | boundary (a : Bool) (k : Fin n)
  deriving DecidableEq

variable {n : ℕ}

def dimension : Cell n → ℕ
  | .top => n
  | .boundary _ k => k.val

theorem dimension_le (x : Cell n) : dimension x ≤ n := by
  cases x with
  | top => exact le_rfl
  | boundary a k => exact k.isLt.le

def face (a : Bool) (m : ℕ) (x : Cell n) : Cell n :=
  if h : dimension x ≤ m then x
  else .boundary a ⟨m, lt_of_lt_of_le (Nat.lt_of_not_ge h) (dimension_le x)⟩

@[simp] theorem face_of_dimension_le (a : Bool) (m : ℕ) (x : Cell n)
    (h : dimension x ≤ m) : face a m x = x := dite_eq_left h

@[simp] theorem dimension_face (a : Bool) (m : ℕ) (x : Cell n) :
    dimension (face a m x) = min m (dimension x) := by
  unfold face
  split_ifs with h
  · exact (min_eq_right h).symm
  · exact (min_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge h))).symm

theorem globular (a b : Bool) (m k : ℕ) (x : Cell n) :
    face a m (face b k x) = if m < k then face a m x else face b k x := by
  by_cases hx : dimension x ≤ k
  · rw [face_of_dimension_le b k x hx]
    split_ifs with hmk
    · rfl
    · exact face_of_dimension_le a m x (hx.trans (Nat.le_of_not_gt hmk))
  · have hk : k < n := lt_of_lt_of_le (Nat.lt_of_not_ge hx) (dimension_le x)
    have hb : face b k x = Cell.boundary b ⟨k, hk⟩ := dite_eq_right hx
    rw [hb]
    by_cases hmk : m < k
    · rw [ite_eq_left hmk]
      have hm : ¬ dimension x ≤ m := by omega
      have ha : face a m x = Cell.boundary a ⟨m, lt_trans hmk hk⟩ := dite_eq_right hm
      have hab : face a m (Cell.boundary b ⟨k, hk⟩) =
          Cell.boundary a ⟨m, lt_trans hmk hk⟩ := dite_eq_right (Nat.not_le.mpr hmk)
      exact hab.trans ha.symm
    · rw [ite_eq_right hmk]
      exact face_of_dimension_le a m _ (Nat.le_of_not_gt hmk)

/-- Matching faces force at least one factor to be a unit at that level. -/
theorem matching_unit {m : ℕ} {x y : Cell n}
    (h : face true m x = face false m y) : dimension x ≤ m ∨ dimension y ≤ m := by
  by_contra hn
  have hx : ¬ dimension x ≤ m := fun hx => hn (Or.inl hx)
  have hy : ¬ dimension y ≤ m := fun hy => hn (Or.inr hy)
  unfold face at h
  rw [dite_eq_right hx, dite_eq_right hy] at h
  cases h

def comp (m : ℕ) (x y : Cell n) : Cell n := if dimension x ≤ m then y else x

theorem source_comp (m : ℕ) (x y : Cell n)
    (h : face true m x = face false m y) :
    face false m (comp m x y) = face false m x := by
  by_cases hx : dimension x ≤ m
  · simpa only [comp, ite_eq_left hx, face_of_dimension_le _ _ _ hx] using h.symm
  · simp only [comp, ite_eq_right hx]

theorem target_comp (m : ℕ) (x y : Cell n)
    (h : face true m x = face false m y) :
    face true m (comp m x y) = face true m y := by
  by_cases hx : dimension x ≤ m
  · simp only [comp, ite_eq_left hx]
  · have hy := (matching_unit h).resolve_left hx
    simpa only [comp, ite_eq_right hx, face_of_dimension_le _ _ _ hy] using h

theorem face_comp (a : Bool) (m k : ℕ) (hkm : k < m) (x y : Cell n) :
    face a m (comp k x y) = comp k (face a m x) (face a m y) := by
  by_cases hx : dimension x ≤ k
  · have hx' : dimension (face a m x) ≤ k := by rw [dimension_face]; omega
    simp only [comp, ite_eq_left hx, ite_eq_left hx']
  · have hx' : ¬ dimension (face a m x) ≤ k := by rw [dimension_face]; omega
    simp only [comp, ite_eq_right hx, ite_eq_right hx']

theorem left_unit (m : ℕ) (x : Cell n) : comp m (face false m x) x = x := by
  have h : dimension (face false m x) ≤ m := by rw [dimension_face]; exact min_le_left _ _
  exact ite_eq_left h

theorem right_unit (m : ℕ) (x : Cell n) : comp m x (face true m x) = x := by
  unfold comp
  split_ifs with h
  · exact face_of_dimension_le true m x h
  · rfl

theorem assoc (m : ℕ) (x y z : Cell n) :
    comp m (comp m x y) z = comp m x (comp m y z) := by
  by_cases hx : dimension x ≤ m <;> simp only [comp, hx, ite_true, ite_false]

theorem matching_small_iff {m k : ℕ} (hmk : m < k) {x y : Cell n}
    (h : face true k x = face false k y) :
    dimension x ≤ m ↔ dimension y ≤ m := by
  have hd := congrArg dimension h
  rw [dimension_face, dimension_face] at hd
  omega

theorem interchange (m k : ℕ) (hmk : m < k) (a b c d : Cell n)
    (hac : face true k a = face false k c) :
    comp k (comp m a b) (comp m c d) = comp m (comp k a c) (comp k b d) := by
  have he := matching_small_iff hmk hac
  by_cases ha : dimension a ≤ m
  · have hc := he.mp ha
    have ha' : dimension a ≤ k := ha.trans hmk.le
    simp only [comp, ite_eq_left ha, ite_eq_left hc, ite_eq_left ha']
  · have hc : ¬ dimension c ≤ m := fun hc => ha (he.mpr hc)
    have ht : ¬ dimension (comp k a c) ≤ m := by
      unfold comp
      split_ifs <;> assumption
    rw [show comp m a b = a from ite_eq_right ha,
      show comp m c d = c from ite_eq_right hc]
    exact (ite_eq_right ht).symm

/-- The strict n-globe, with its actual finite boundary cells. -/
def category (n : ℕ) : StrictOmegaCategory where
  Cell := Cell n
  face := face
  comp m x y _ := comp m x y
  globular := globular
  source_comp := source_comp
  target_comp := target_comp
  face_comp a m k h x y _ _ := face_comp a m k h x y
  left_unit m x _ := left_unit m x
  right_unit m x _ := right_unit m x
  assoc m x y z _ _ _ _ := assoc m x y z
  interchange m k h a b c d _ _ hac _ _ _ := interchange m k h a b c d hac
  finite_dimension x := ⟨dimension x, face_of_dimension_le _ _ _ le_rfl,
    face_of_dimension_le _ _ _ le_rfl⟩

theorem category_truncated (n : ℕ) : (category n).IsTruncated n := by
  intro x
  exact ⟨face_of_dimension_le false n x (dimension_le x),
    face_of_dimension_le true n x (dimension_le x)⟩

end Thomason.Construction.StrictOmegaCategory.Globe

end

section

/-! # Universal cells of the strict globes

Strict functors from the n-globe are exactly cells of dimension at most n.
The bijection is given by evaluation at the actual top cell, and is natural
under every strict functor. These are the generating parameters for the
right Gray interval construction and its internal hom.
-/

namespace Thomason.Construction.StrictOmegaCategory.Globe

open CategoryTheory

variable (C : StrictOmegaCategory) {n : ℕ}

def evaluate (x : C) : Cell n → C
  | .top => x
  | .boundary a k => C.face a k x

@[simp] theorem evaluate_top (x : C) : evaluate C (n := n) x .top = x := rfl

@[simp] theorem evaluate_boundary (x : C) (a : Bool) (k : Fin n) :
    evaluate C x (.boundary a k) = C.face a k x := rfl

theorem evaluate_dimension (x : C) (hx : C.DimensionLE n x) (s : Cell n) :
    C.DimensionLE (dimension s) (evaluate C x s) := by
  cases s with
  | top => exact hx
  | boundary a k => exact C.face_dimensionLE a k x

theorem evaluate_face (x : C) (hx : C.DimensionLE n x)
    (a : Bool) (m : ℕ) (s : Cell n) :
    evaluate C x (face a m s) = C.face a m (evaluate C x s) := by
  by_cases hs : dimension s ≤ m
  · rw [face_of_dimension_le a m s hs]
    have hm := C.dimensionLE_mono hs (evaluate_dimension C x hx s)
    cases a
    · exact hm.1.symm
    · exact hm.2.symm
  · have hm : m < dimension s := Nat.lt_of_not_ge hs
    have hmn : m < n := lt_of_lt_of_le hm (dimension_le s)
    rw [show face a m s = Cell.boundary a ⟨m, hmn⟩ from dite_eq_right hs]
    cases s with
    | top => rfl
    | boundary b k =>
      change C.face a m x = C.face a m (C.face b k x)
      exact (C.globular a b m k x).trans (ite_eq_left hm) |>.symm

private theorem comp_of_left_unit (m : ℕ) (s t : C)
    (h : C.target m s = C.source m t) (hs : s = C.source m t) :
    C.comp m s t h = t := by
  subst s
  exact C.left_unit m t h

private theorem comp_of_right_unit (m : ℕ) (s t : C)
    (h : C.target m s = C.source m t) (ht : t = C.target m s) :
    C.comp m s t h = s := by
  subst t
  exact C.right_unit m s h

/-- The strict functor determined by a chosen n-dimensional cell. -/
def lift (x : C) (hx : C.DimensionLE n x) : category n ⟶ C where
  toFun := evaluate C x
  map_face := evaluate_face C x hx
  map_comp m s t h h' := by
    change evaluate C x (comp m s t) =
      C.comp m (evaluate C x s) (evaluate C x t) h'
    have he : C.target m (evaluate C x s) = C.source m (evaluate C x t) := h'
    by_cases hs : dimension s ≤ m
    · have hd := C.dimensionLE_mono hs (evaluate_dimension C x hx s)
      have heq : evaluate C x s = C.source m (evaluate C x t) := hd.2.symm.trans he
      rw [show Globe.comp m s t = t from ite_eq_left hs]
      exact (comp_of_left_unit C m _ _ h' heq).symm
    · have ht := (matching_unit h).resolve_left hs
      have hd := C.dimensionLE_mono ht (evaluate_dimension C x hx t)
      have heq : evaluate C x t = C.target m (evaluate C x s) := hd.1.symm.trans he.symm
      rw [show Globe.comp m s t = s from ite_eq_right hs]
      exact (comp_of_right_unit C m _ _ h' heq).symm

@[simp] theorem lift_top (x : C) (hx : C.DimensionLE n x) : (lift C x hx).toFun .top = x := rfl

/-- Evaluation at the top cell determines a strict functor on the whole globe. -/
theorem hom_ext (f g : category n ⟶ C)
    (h : f.toFun .top = g.toFun .top) : f = g := by
  apply Hom.ext
  funext s
  cases s with
  | top => exact h
  | boundary a k =>
    have hs : face a k (Cell.top : Cell n) = Cell.boundary a k := by
      exact dite_eq_right (Nat.not_le.mpr k.isLt)
    change f.toFun (Cell.boundary a k) = g.toFun (Cell.boundary a k)
    calc
      f.toFun (Cell.boundary a k) = C.face a k (f.toFun Cell.top) :=
        (congrArg f.toFun hs).symm.trans (f.map_face a k Cell.top)
      _ = C.face a k (g.toFun Cell.top) := congrArg (C.face a k) h
      _ = g.toFun (Cell.boundary a k) :=
        (g.map_face a k Cell.top).symm.trans (congrArg g.toFun hs)

/-- The globe represents bounded cells in the actual strict category. -/
def homEquiv (n : ℕ) : (category n ⟶ C) ≃ {x : C // C.DimensionLE n x} where
  toFun f := ⟨f.toFun .top, f.dimensionLE (category_truncated n Cell.top)⟩
  invFun x := lift C x.val x.property
  left_inv f := hom_ext C _ _ rfl
  right_inv x := by apply Subtype.ext; rfl

@[simp] theorem homEquiv_naturality {D : StrictOmegaCategory} (F : C ⟶ D)
    (n : ℕ) (f : category n ⟶ C) :
    ((homEquiv D n) (f ≫ F)).val = F.toFun ((homEquiv C n f).val) := rfl

end Thomason.Construction.StrictOmegaCategory.Globe

end

section

/-! # The augmented directed complex of a globe

There are two positive basis elements below the top dimension and one at
the top. Every basis boundary is target minus source. This is the finite
chain parameter used for the right interval tensor on the free globes.
-/

namespace Thomason.Construction.DirectedGlobeComplex

open CategoryTheory

abbrev Basis (n k : ℕ) := {a : Bool // k < n ∨ (k = n ∧ a = false)}
abbrev Chains (n k : ℕ) := Basis n k →₀ ℤ

noncomputable def weight (n k : ℕ) : Chains n k →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ => 1)

@[simp] theorem weight_single (n k : ℕ) (s : Basis n k) (z : ℤ) :
    weight n k (Finsupp.single s z) = z := by simp [weight]

noncomputable def boundary (n k : ℕ) : Chains n k :=
  if hk : k < n then
    Finsupp.single ⟨true, Or.inl hk⟩ 1 - Finsupp.single ⟨false, Or.inl hk⟩ 1
  else 0

@[simp] theorem weight_boundary (n k : ℕ) : weight n k (boundary n k) = 0 := by
  classical
  unfold boundary
  split_ifs <;> simp

noncomputable def differential (n k : ℕ) : Chains n (k+1) →ₗ[ℤ] Chains n k :=
  Finsupp.linearCombination ℤ (fun _ => boundary n k)

@[simp] theorem differential_single (n k : ℕ) (s : Basis n (k+1)) (z : ℤ) :
    differential n k (Finsupp.single s z) = z • boundary n k := by
  simp [differential]

theorem differential_eq_weight (n k : ℕ) (x : Chains n (k+1)) :
    differential n k x = weight n (k+1) x • boundary n k := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, add_smul]
  | single s z => simp

@[simp] theorem weight_differential (n k : ℕ) (x : Chains n (k+1)) :
    weight n k (differential n k x) = 0 := by
  rw [differential_eq_weight]
  simp

theorem differential_squared (n k : ℕ) (x : Chains n (k+2)) :
    differential n k (differential n (k+1) x) = 0 := by
  rw [differential_eq_weight]
  simp

def positive (n k : ℕ) : AddSubmonoid (Chains n k) where
  carrier := {x | ∀ s, 0 ≤ x s}
  zero_mem' := fun _ => le_rfl
  add_mem' hx hy s := add_nonneg (hx s) (hy s)

noncomputable def complex (n : ℕ) : DirectedComplex where
  group k := AddCommGrpCat.of (Chains n k)
  differential k := (differential n k).toAddMonoidHom
  differential_squared := differential_squared n
  augmentation := (weight n 0).toAddMonoidHom
  augmentation_differential := weight_differential n 0
  positive := positive n

theorem chains_eq_zero_above {n k : ℕ} (h : n < k) (x : Chains n k) : x = 0 := by
  ext s
  rcases s.property with hs | ⟨hs, _⟩ <;> omega

noncomputable def topTable (n : ℕ) (a : Bool) (k : ℕ) : Chains n k :=
  if hk : k < n then Finsupp.single ⟨a, Or.inl hk⟩ 1
  else if he : k = n then Finsupp.single ⟨false, Or.inr ⟨he, rfl⟩⟩ 1
  else 0

theorem topTable_boundary (n k : ℕ) (a : Bool) :
    differential n k (topTable n a (k+1)) = topTable n true k - topTable n false k := by
  classical
  by_cases hk : k < n
  · by_cases hs : k+1 < n
    · simp [topTable, hs, hk, boundary]
    · have he : k+1 = n := by omega
      simp [topTable, he, hk, boundary]
  · have hs : ¬ k+1 < n := by omega
    have he : k+1 ≠ n := by omega
    by_cases hkn : k = n
    · simp [topTable, hkn]
    · simp [topTable, hk, hs, he, hkn]

/-- The universal n-cell is the positive table of its two faces in every
lower degree and the single generator at its top degree. -/
noncomputable def topCell (n : ℕ) : (complex n).realization where
  table := topTable n
  positive a k := by
    classical
    change ∀ s, 0 ≤ topTable n a k s
    intro s
    unfold topTable
    split_ifs
    · simp only [Finsupp.single_apply]
      split_ifs <;> norm_num
    · simp only [Finsupp.single_apply]
      split_ifs <;> norm_num
    · exact le_rfl
  augmentation a := by
    change weight n 0 (topTable n a 0) = 1
    unfold topTable
    split_ifs with h h'
    · simp
    · simp
    · omega
  boundary a k := topTable_boundary n k a
  finite_support := ⟨n, fun k hk a => by
    simp [topTable, Nat.not_lt.mpr hk.le, Nat.ne_of_gt hk]
    rfl⟩

theorem topCell_dimension (n : ℕ) : (complex n).realization.DimensionLE n (topCell n) := by
  have hf (a : Bool) : (topCell n).face a n = topCell n := by
    apply DirectedComplex.Cell.ext
    funext b k
    change DirectedComplex.Cell.cutTable (topCell n) a n b k = topTable n b k
    by_cases hk : k < n
    · simp only [DirectedComplex.Cell.cutTable, hk, ite_true]
      rfl
    · by_cases he : k = n
      · subst k
        cases a <;> cases b <;> simp [DirectedComplex.Cell.cutTable, topCell, topTable] <;> rfl
      · have hnk : n < k := by omega
        simp [DirectedComplex.Cell.cutTable, hk, he, topTable]
        rfl
  exact ⟨hf false, hf true⟩

/-- The actual positive-table realization of the free globe receives its
canonical strict cell map, with no Gray input. -/
noncomputable def fromGlobe (n : ℕ) :
    StrictOmegaCategory.Globe.category n ⟶ (complex n).realization :=
  StrictOmegaCategory.Globe.lift _ (topCell n) (topCell_dimension n)

end Thomason.Construction.DirectedGlobeComplex

end

section

/-! # Positive globe maps and bounded cells

A positive chain map from the n-globe complex is the full chain table of
one bounded cell. The construction preserves all signed boundaries and
augmentation equations before taking strict realization.
-/

namespace Thomason.Construction.DirectedGlobeComplex

open CategoryTheory _root_.OAI.Thomason.Construction.DirectedComplex

noncomputable section

variable {K : DirectedComplex.{0}}

/-- Extend the table entries of a cell linearly on the globe basis. -/
def cellApp (n : ℕ) (x : Cell K) (k : ℕ) : Chains n k →ₗ[ℤ] K.group k :=
  Finsupp.linearCombination ℤ (fun s => x.table s.val k)

@[simp] theorem cellApp_single (n : ℕ) (x : Cell K) (k : ℕ) (s : Basis n k) (z : ℤ) :
    cellApp n x k (Finsupp.single s z) = z • x.table s.val k := by
  simp [cellApp]

theorem cellApp_boundary (n : ℕ) (x : Cell K) (k : ℕ) (hk : k < n) :
    cellApp n x k (boundary n k) = x.table true k - x.table false k := by
  simp [boundary, hk]

theorem cellApp_differential (n : ℕ) (x : Cell K) (k : ℕ) (u : Chains n (k+1)) :
    cellApp n x k (differential n k u) = K.differential k (cellApp n x (k+1) u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single s z =>
    have hk : k < n := by rcases s.property with h | ⟨h, _⟩ <;> omega
    simp only [differential_single, map_smul, cellApp_single, map_zsmul]
    rw [cellApp_boundary n x k hk, x.boundary]

theorem cellApp_augmentation (n : ℕ) (x : Cell K) (u : Chains n 0) :
    K.augmentation (cellApp n x 0 u) = weight n 0 u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single s z => simp [x.augmentation]

theorem cellApp_positive (n : ℕ) (x : Cell K) (k : ℕ) (u : Chains n k)
    (hu : u ∈ positive n k) : cellApp n x k u ∈ K.positive k := by
  classical
  change (u.sum fun s z => z • x.table s.val k) ∈ K.positive k
  apply (K.positive k).sum_mem
  intro s hs
  change u s • x.table s.val k ∈ K.positive k
  rw [← Int.toNat_of_nonneg (hu s), natCast_zsmul]
  exact (K.positive k).nsmul_mem (x.positive s.val k) _

/-- The canonical positive globe map associated to a cell table. Its top
cell is the n-source of the table, hence the table itself when bounded. -/
def cellMap (n : ℕ) (x : Cell K) : Hom (complex n) K where
  app k := (cellApp n x k).toAddMonoidHom
  differential := cellApp_differential n x
  augmentation := cellApp_augmentation n x
  positive k _ hu := cellApp_positive n x k _ hu

/-- Realizing the associated positive chain map recovers the full bounded
table, including the lower-dimensional identity extensions. -/
theorem cellMap_top (n : ℕ) (x : Cell K) :
    (cellMap n x).realization.toFun (topCell n) = x.face false n := by
  apply Cell.ext
  funext a k
  change cellApp n x k (topTable n a k) = Cell.cutTable x false n a k
  by_cases hk : k < n
  · simp [topTable, hk, Cell.cutTable]
  · by_cases he : k = n
    · subst k
      simp [topTable, Cell.cutTable]
    · simp [topTable, hk, he, Cell.cutTable]

theorem cellMap_top_of_bounded (n : ℕ) (x : Cell K)
    (hx : K.realization.DimensionLE n x) :
    (cellMap n x).realization.toFun (topCell n) = x :=
  (cellMap_top n x).trans hx.1

end

end Thomason.Construction.DirectedGlobeComplex

end

end OAI
