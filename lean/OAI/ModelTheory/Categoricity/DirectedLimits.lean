import OAI.ModelTheory.Categoricity.ArrayIsomorphisms

namespace OAI

/-!
# Directed limits of finite-support arrays

The index, base and six-sorted carrier are constructed as directed limits.
Finite tuples and supports can be represented in a common stage. Compatible
row and column actions give the limit its relational interpretation, and
convexity supplies local countability and the strong-embedding properties.
-/

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace LimitTools

variable {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J]
  {F : J → Type u} (f : ∀ i j, i ≤ j → F i ↪ F j) [DirectedSystem F (f · · ·)]
  (inj : ∀ i j h, Function.Injective (f i j h))

abbrev Limit := DirectLimit F f

def of (i : J) : F i ↪ Limit f := ⟨fun x => ⟦⟨i, x⟩⟧, DirectLimit.mk_injective f inj i⟩

omit [Nonempty J] in
@[simp] theorem of_map (i j : J) (h : i ≤ j) (x : F i) :
    of f inj j (f i j h x) = of f inj i x := by
  exact DirectLimit.mk_apply (f := f) i j x h

theorem common {A : Type v} [Finite A] (x : A → Limit f) (i : J) :
    ∃ j, i ≤ j ∧ ∃ y : A → F j, ∀ a, of f inj j (y a) = x a := by
  classical
  let r (a : A) : Σ j, F j := Classical.choose (Quotient.exists_rep (x a))
  have hr (a : A) : (⟦r a⟧ : Limit f) = x a := Classical.choose_spec (Quotient.exists_rep (x a))
  let _ := Fintype.ofFinite A
  obtain ⟨j, hj⟩ := (insert i (Finset.univ.image (fun a => (r a).1))).exists_le
  have hij : i ≤ j := hj i (Finset.mem_insert_self _ _)
  have ha (a : A) : (r a).1 ≤ j := hj _ (Finset.mem_insert_of_mem (Finset.mem_image.2
    ⟨a, Finset.mem_univ a, rfl⟩))
  exact ⟨j, hij, fun a => f _ _ (ha a) (r a).2,
    fun a => (of_map f inj _ _ _ _).trans (hr a)⟩

end LimitTools

namespace Arrays
namespace System

variable {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J]

structure Data where
  obj : J → Arrays.Data.{u}
  map : ∀ i j, i ≤ j → Map (obj i) (obj j)
  map_id : ∀ i, map i i le_rfl = Map.id (obj i)
  map_comp : ∀ i j k (h : i ≤ j) (h' : j ≤ k),
    (map j k h').comp (map i j h) = map i k (h.trans h')

namespace Data

open Tuples

variable (S : Data (J := J))

def indexMap (i j : J) (h : i ≤ j) : (S.obj i).I ↪ (S.obj j).I := (S.map i j h).index

def baseMap (i j : J) (h : i ≤ j) : (S.obj i).B ↪ (S.obj j).B := (S.map i j h).base.toEmbedding

def pointMap (i j : J) (h : i ≤ j) : (S.obj i).Carrier ↪ (S.obj j).Carrier :=
  (S.map i j h).toEmbedding

instance indexSystem : DirectedSystem (fun i => (S.obj i).I) (S.indexMap · · ·) where
  map_self := by intro i x; change (S.map i i le_rfl).index x = x; rw [S.map_id]; rfl
  map_map := by
    intro k j i h h' x
    exact congrArg (fun f : Map (S.obj i) (S.obj k) => f.index x) (S.map_comp i j k h h')

instance baseSystem : DirectedSystem (fun i => (S.obj i).B) (S.baseMap · · ·) where
  map_self := by intro i x; change (S.map i i le_rfl).base x = x; rw [S.map_id]; rfl
  map_map := by
    intro k j i h h' x
    exact congrArg (fun f : Map (S.obj i) (S.obj k) => f.base x) (S.map_comp i j k h h')

instance pointSystem : DirectedSystem (fun i => (S.obj i).Carrier) (S.pointMap · · ·) where
  map_self := by intro i x; change (S.map i i le_rfl).onPoint x = x; rw [S.map_id, Map.id_onPoint]
  map_map := by
    intro k j i h h' x
    change (S.map j k h').onPoint ((S.map i j h).onPoint x) = _
    rw [← Map.comp_onPoint, S.map_comp]
    rfl

abbrev I := DirectLimit (fun i => (S.obj i).I) S.indexMap
abbrev B := DirectLimit (fun i => (S.obj i).B) S.baseMap
abbrev X := DirectLimit (fun i => (S.obj i).Carrier) S.pointMap

def index (i : J) : (S.obj i).I ↪ S.I :=
  LimitTools.of S.indexMap (fun a b h => (S.map a b h).index.injective) i

def base (i : J) : (S.obj i).B ↪ S.B :=
  LimitTools.of S.baseMap (fun a b h => (S.map a b h).base.injective) i

def point (i : J) : (S.obj i).Carrier ↪ S.X :=
  LimitTools.of S.pointMap (fun a b h => (S.map a b h).injective) i

omit [Nonempty J] in
@[simp] theorem index_map (i j : J) (h : i ≤ j) (x : (S.obj i).I) :
    S.index j ((S.map i j h).index x) = S.index i x := LimitTools.of_map S.indexMap _ i j h x

omit [Nonempty J] in
@[simp] theorem base_map (i j : J) (h : i ≤ j) (x : (S.obj i).B) :
    S.base j ((S.map i j h).base x) = S.base i x := LimitTools.of_map S.baseMap _ i j h x

omit [Nonempty J] in
@[simp] theorem point_map (i j : J) (h : i ≤ j) (x : (S.obj i).Carrier) :
    S.point j ((S.map i j h).onPoint x) = S.point i x := LimitTools.of_map S.pointMap _ i j h x

instance : Nonempty S.I := ⟨S.index (Classical.arbitrary J) (Classical.arbitrary _)⟩
instance : Nonempty S.B := ⟨S.base (Classical.arbitrary J) (Classical.arbitrary _)⟩

def le : S.B → S.B → Prop := DirectLimit.lift₂ S.baseMap S.baseMap (fun _ a b => a ≤ b)
  (fun i j h _a _b => propext (S.map i j h).base.le_iff_le.symm)

omit [Nonempty J] in
@[simp] theorem le_base (i : J) (a b : (S.obj i).B) : S.le (S.base i a) (S.base i b) ↔ a ≤ b := by
  unfold le
  change DirectLimit.lift₂ S.baseMap S.baseMap (fun _ a b => a ≤ b) _ ⟦⟨i, a⟩⟧ ⟦⟨i, b⟩⟧ ↔ _
  rw [DirectLimit.lift₂_def]

instance leInstance : LE S.B := ⟨S.le⟩
instance ltInstance : LT S.B := ⟨fun a b => S.le a b ∧ ¬ S.le b a⟩

instance order : LinearOrder S.B where
  le := S.le
  lt := fun a b => S.le a b ∧ ¬ S.le b a
  lt_iff_le_not_ge := by intros; rfl
  le_refl := DirectLimit.induction _ (fun i a => (S.le_base i a a).2 le_rfl)
  le_trans := by
    intro a b c
    induction a, b, c using DirectLimit.induction₃ S.baseMap with
    | ih i a b c =>
      change S.le (S.base i a) (S.base i b) → S.le (S.base i b) (S.base i c) → _
      rw [S.le_base, S.le_base]
      intro h h'; exact (S.le_base i a c).2 (h.trans h')
  le_antisymm := by
    intro a b
    induction a, b using DirectLimit.induction₂ S.baseMap with
    | ih i a b =>
      change S.le (S.base i a) (S.base i b) → S.le (S.base i b) (S.base i a) → _
      rw [le_base, le_base]
      intro h h'; exact congrArg (S.base i) (le_antisymm h h')
  le_total := by
    intro a b
    induction a, b using DirectLimit.induction₂ S.baseMap with
    | ih i a b =>
      change S.le (S.base i a) (S.base i b) ∨ S.le (S.base i b) (S.base i a)
      rw [le_base, le_base]; exact le_total a b
  toDecidableLE := Classical.decRel _

instance preorder : Preorder S.B := S.order.toPartialOrder.toPreorder

def baseOrder (i : J) : (S.obj i).B ↪o S.B where
  toEmbedding := S.base i
  map_rel_iff' := by
    intro a b
    exact S.le_base i a b

omit [Nonempty J] in
@[simp] theorem tuple_map (i j : J) (h : i ≤ j) (t : Tuple (S.obj i).I) :
    Tuples.map (S.index j) (Tuples.map (S.map i j h).index t) = Tuples.map (S.index i) t := by
  rw [Tuples.map_comp]
  congr 1
  ext x
  exact S.index_map i j h x

omit [Nonempty J] in
@[simp] theorem finset_map (i j : J) (h : i ≤ j) (s : Finset (S.obj i).B) :
    (s.map (S.map i j h).base.toEmbedding).map (S.base j) = s.map (S.base i) := by
  rw [Finset.map_map]
  congr 1
  ext x
  exact S.base_map i j h x

theorem tuple_exists (t : Tuple S.I) (i : J) :
    ∃ j, i ≤ j ∧ ∃ r : Tuple (S.obj j).I, Tuples.map (S.index j) r = t := by
  obtain ⟨j, hij, y, hy⟩ := LimitTools.common S.indexMap
    (fun a b h => (S.map a b h).index.injective) (fun a => t.2 a) i
  have hinj : Function.Injective y := by
    intro a b h
    apply t.2.injective
    rw [← hy a, ← hy b, h]
  exact ⟨j, hij, ⟨t.1, ⟨y, hinj⟩⟩, by
    cases t with
    | mk k t =>
      change (⟨k, _⟩ : Tuple S.I) = ⟨k, t⟩
      congr 1
      exact Function.Embedding.ext hy⟩

theorem finset_exists (s : Finset S.B) (i : J) :
    ∃ j, i ≤ j ∧ ∃ r : Finset (S.obj j).B, r.map (S.base j) = s := by
  classical
  obtain ⟨j, hij, y, hy⟩ := LimitTools.common S.baseMap
    (fun a b h => (S.map a b h).base.injective) (fun a : s => (a : S.B)) i
  refine ⟨j, hij, Finset.univ.image y, ?_⟩
  ext b
  simp only [Finset.mem_map, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ⟨c, rfl⟩, he⟩
    have hc : S.base j (y c) = (c : S.B) := hy c
    rw [hc] at he
    exact he ▸ c.property
  · intro hb
    exact ⟨y ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩, hy ⟨b, hb⟩⟩

open scoped symmDiff
local instance : DecidableEq S.B := Classical.decEq _
local instance (i : J) : DecidableEq (S.obj i).B := Classical.decEq _
local instance (i : J) : DecidableEq (Tuple (S.obj i).I) := Classical.decEq _

def shapeAt (i : J) : (S.obj i).Carrier → Point S.I S.B
  | .index a => .index (S.index i a)
  | .base b => .base (S.base i b)
  | .group s => .group (s.map (S.base i))
  | .star v => .star v
  | .row t n _ => .row (Tuples.map (S.index i) t) n ∅
  | .col t b _ => .col (Tuples.map (S.index i) t) (S.base i b) ∅

omit [Nonempty J] in
theorem shapeAt_map (i j : J) (h : i ≤ j) (x : (S.obj i).Carrier) :
    S.shapeAt j ((S.map i j h).onPoint x) = S.shapeAt i x := by
  cases x <;> simp only [Map.onPoint, shapeAt, index_map, base_map, tuple_map, finset_map]

def shape : S.X → Point S.I S.B := DirectLimit.lift S.pointMap S.shapeAt
  (fun i j h x => (S.shapeAt_map i j h x).symm)

omit [Nonempty J] in
@[simp] theorem shape_point (i : J) (x : (S.obj i).Carrier) :
    S.shape (S.point i x) = S.shapeAt i x := rfl

def rowDiffAt (i : J) : (S.obj i).Carrier → (S.obj i).Carrier → Option (Finset S.B)
  | .row t n s, .row r m q => if t = r ∧ n = m then some ((s ∆ q).map (S.base i)) else none
  | _, _ => none

def colDiffAt (i : J) : (S.obj i).Carrier → (S.obj i).Carrier → Option (Finset ℕ)
  | .col t b v, .col r c w => if t = r ∧ b = c then some (v ∆ w) else none
  | _, _ => none

omit [Nonempty J] in
theorem rowDiffAt_map (i j : J) (h : i ≤ j) (x y : (S.obj i).Carrier) :
    S.rowDiffAt j ((S.map i j h).onPoint x) ((S.map i j h).onPoint y) = S.rowDiffAt i x y := by
  classical
  cases x <;> cases y <;> simp only [Map.onPoint, rowDiffAt]
  case row.row t n s r m q =>
    by_cases ht : t = r
    · subst r
      by_cases hn : n = m
      · subst m
        simp only [and_self, ↓reduceIte]
        rw [symmDiff_symmDiff_symmDiff_comm, symmDiff_self, bot_symmDiff,
          ← FiniteSupports.map_symmDiff, finset_map]
      · simp only [hn, and_false, ↓reduceIte]
    · simp only [(Tuples.map_injective (S.map i j h).index).eq_iff, ht, false_and, ↓reduceIte]

omit [IsDirectedOrder J] [Nonempty J] in
theorem colDiffAt_map (i j : J) (h : i ≤ j) (x y : (S.obj i).Carrier) :
    S.colDiffAt j ((S.map i j h).onPoint x) ((S.map i j h).onPoint y) = S.colDiffAt i x y := by
  classical
  cases x <;> cases y <;> simp only [Map.onPoint, colDiffAt]
  case col.col t b v r c w =>
    by_cases ht : t = r
    · subst r
      by_cases hb : b = c
      · subst c
        simp only [and_self, ↓reduceIte]
        rw [symmDiff_symmDiff_symmDiff_comm, symmDiff_self, bot_symmDiff]
      · simp only [(S.map i j h).base.injective.eq_iff, hb, and_false, ↓reduceIte]
    · simp only [(Tuples.map_injective (S.map i j h).index).eq_iff, ht, false_and, ↓reduceIte]

def rowDiff : S.X → S.X → Option (Finset S.B) :=
  DirectLimit.lift₂ S.pointMap S.pointMap S.rowDiffAt (fun i j h x y => (S.rowDiffAt_map i j h x y).symm)

def colDiff : S.X → S.X → Option (Finset ℕ) :=
  DirectLimit.lift₂ S.pointMap S.pointMap S.colDiffAt (fun i j h x y => (S.colDiffAt_map i j h x y).symm)

omit [Nonempty J] in
@[simp] theorem rowDiff_point (i : J) (x y : (S.obj i).Carrier) :
    S.rowDiff (S.point i x) (S.point i y) = S.rowDiffAt i x y := by
  exact DirectLimit.lift₂_def S.pointMap S.pointMap S.rowDiffAt _ i x y

omit [Nonempty J] in
@[simp] theorem colDiff_point (i : J) (x y : (S.obj i).Carrier) :
    S.colDiff (S.point i x) (S.point i y) = S.colDiffAt i x y := by
  exact DirectLimit.lift₂_def S.pointMap S.pointMap S.colDiffAt _ i x y

omit [Nonempty J] in
theorem rowDiff_refl_at (i : J) (t : Tuple (S.obj i).I) (n : ℕ) (s q : Finset (S.obj i).B) :
    S.rowDiff (S.point i (.row t n s)) (S.point i (.row t n q)) =
      some ((s ∆ q).map (S.base i)) := by
  simp only [rowDiff_point, rowDiffAt, and_self, ↓reduceIte]

omit [Nonempty J] in
theorem colDiff_refl_at (i : J) (t : Tuple (S.obj i).I) (b : (S.obj i).B) (v w : Finset ℕ) :
    S.colDiff (S.point i (.col t b v)) (S.point i (.col t b w)) = some (v ∆ w) := by
  simp only [colDiff_point, colDiffAt, and_self, ↓reduceIte]

omit [Nonempty J] in
theorem rowDiff_zero {x y : S.X} (h : S.rowDiff x y = some ∅) : x = y := by
  induction x, y using DirectLimit.induction₂ S.pointMap with
  | ih i x y =>
    change S.rowDiff (S.point i x) (S.point i y) = some ∅ at h
    rw [rowDiff_point] at h
    cases x <;> cases y <;> simp only [rowDiffAt] at h
    all_goals try contradiction
    case row.row t n s r m q =>
      split_ifs at h with he
      · obtain ⟨rfl, rfl⟩ := he
        have hs : s = q := Finset.symmDiff_eq_empty.1 (by
          have hh := Option.some.inj h
          simpa using hh)
        subst q
        rfl

omit [Nonempty J] in
theorem colDiff_zero {x y : S.X} (h : S.colDiff x y = some ∅) : x = y := by
  induction x, y using DirectLimit.induction₂ S.pointMap with
  | ih i x y =>
    change S.colDiff (S.point i x) (S.point i y) = some ∅ at h
    rw [colDiff_point] at h
    cases x <;> cases y <;> simp only [colDiffAt] at h
    all_goals try contradiction
    case col.col t b v r c w =>
      split_ifs at h with he
      · obtain ⟨rfl, rfl⟩ := he
        have hv : v = w := Finset.symmDiff_eq_empty.1 (Option.some.inj h)
        subst w
        rfl

omit [Nonempty J] in
theorem rowDiff_symm (x y : S.X) : S.rowDiff x y = S.rowDiff y x := by
  induction x, y using DirectLimit.induction₂ S.pointMap with
  | ih i x y =>
    change S.rowDiff (S.point i x) (S.point i y) = S.rowDiff (S.point i y) (S.point i x)
    rw [rowDiff_point, rowDiff_point]
    cases x <;> cases y <;> simp only [rowDiffAt]
    case row.row t n s r m q =>
      by_cases ht : t = r <;> by_cases hn : n = m <;>
        simp_all [symmDiff_comm, eq_comm]

omit [Nonempty J] in
theorem colDiff_symm (x y : S.X) : S.colDiff x y = S.colDiff y x := by
  induction x, y using DirectLimit.induction₂ S.pointMap with
  | ih i x y =>
    change S.colDiff (S.point i x) (S.point i y) = S.colDiff (S.point i y) (S.point i x)
    rw [colDiff_point, colDiff_point]
    cases x <;> cases y <;> simp only [colDiffAt]
    case col.col t b v r c w =>
      by_cases ht : t = r <;> by_cases hb : b = c <;>
        simp_all [symmDiff_comm, eq_comm]

omit [Nonempty J] in
theorem rowDiff_trans {x y z : S.X} {s q : Finset S.B}
    (h : S.rowDiff x y = some s) (h' : S.rowDiff y z = some q) :
    S.rowDiff x z = some (s ∆ q) := by
  induction x, y, z using DirectLimit.induction₃ S.pointMap with
  | ih i x y z =>
    change S.rowDiff (S.point i x) (S.point i y) = some s at h
    change S.rowDiff (S.point i y) (S.point i z) = some q at h'
    change S.rowDiff (S.point i x) (S.point i z) = _
    rw [rowDiff_point] at h h' ⊢
    cases x <;> cases y <;> simp only [rowDiffAt] at h
    all_goals try contradiction
    case row.row t n a r m b =>
      split_ifs at h with he
      · obtain ⟨rfl, rfl⟩ := he
        cases z <;> simp only [rowDiffAt] at h'
        all_goals try contradiction
        case row t' n' c =>
          split_ifs at h' with he'
          · obtain ⟨rfl, rfl⟩ := he'
            have hs := Option.some.inj h
            have hq := Option.some.inj h'
            subst s; subst q
            simp only [rowDiffAt, and_self, ↓reduceIte, ← FiniteSupports.map_symmDiff,
              symmDiff_assoc, symmDiff_symmDiff_cancel_left]

omit [Nonempty J] in
theorem colDiff_trans {x y z : S.X} {v w : Finset ℕ}
    (h : S.colDiff x y = some v) (h' : S.colDiff y z = some w) :
    S.colDiff x z = some (v ∆ w) := by
  induction x, y, z using DirectLimit.induction₃ S.pointMap with
  | ih i x y z =>
    change S.colDiff (S.point i x) (S.point i y) = some v at h
    change S.colDiff (S.point i y) (S.point i z) = some w at h'
    change S.colDiff (S.point i x) (S.point i z) = _
    rw [colDiff_point] at h h' ⊢
    cases x <;> cases y <;> simp only [colDiffAt] at h
    all_goals try contradiction
    case col.col t b a r c d =>
      split_ifs at h with he
      · obtain ⟨rfl, rfl⟩ := he
        cases z <;> simp only [colDiffAt] at h'
        all_goals try contradiction
        case col t' b' e =>
          split_ifs at h' with he'
          · obtain ⟨rfl, rfl⟩ := he'
            have hv := Option.some.inj h
            have hw := Option.some.inj h'
            subst v; subst w
            simp only [colDiffAt, and_self, ↓reduceIte, symmDiff_assoc, symmDiff_symmDiff_cancel_left]

omit [Nonempty J] in
theorem rowDiff_unique {o x y : S.X} {s : Finset S.B}
    (hx : S.rowDiff o x = some s) (hy : S.rowDiff o y = some s) : x = y := by
  apply S.rowDiff_zero
  have h := S.rowDiff_trans ((S.rowDiff_symm x o).trans hx) hy
  simpa only [symmDiff_self, Finset.bot_eq_empty] using h

omit [Nonempty J] in
theorem colDiff_unique {o x y : S.X} {v : Finset ℕ}
    (hx : S.colDiff o x = some v) (hy : S.colDiff o y = some v) : x = y := by
  apply S.colDiff_zero
  have h := S.colDiff_trans ((S.colDiff_symm x o).trans hx) hy
  simpa only [symmDiff_self, Finset.bot_eq_empty] using h

omit [Nonempty J] in

theorem shapeAt_row {i : J} {x : (S.obj i).Carrier} {t : Tuple S.I} {n : ℕ}
    (h : S.shapeAt i x = .row t n ∅) :
    ∃ r s, x = .row r n s ∧ Tuples.map (S.index i) r = t := by
  cases x <;> simp only [shapeAt] at h
  all_goals try contradiction
  case row r m s =>
    obtain ⟨ht, rfl, _⟩ := Point.row.inj h
    exact ⟨r, s, rfl, ht⟩

omit [Nonempty J] in
theorem shapeAt_col {i : J} {x : (S.obj i).Carrier} {t : Tuple S.I} {b : S.B}
    (h : S.shapeAt i x = .col t b ∅) :
    ∃ r c v, x = .col r c v ∧ Tuples.map (S.index i) r = t ∧ S.base i c = b := by
  cases x <;> simp only [shapeAt] at h
  all_goals try contradiction
  case col r c v =>
    obtain ⟨ht, hb, _⟩ := Point.col.inj h
    exact ⟨r, c, v, rfl, ht, hb⟩

omit [Nonempty J] in
theorem rowDiff_exists {x y : S.X} {t : Tuple S.I} {n : ℕ}
    (hx : S.shape x = .row t n ∅) (hy : S.shape y = .row t n ∅) :
    ∃ s, S.rowDiff x y = some s := by
  induction x, y using DirectLimit.induction₂ S.pointMap with
  | ih i x y =>
    obtain ⟨r, s, rfl, hr⟩ := S.shapeAt_row (i := i) (x := x) hx
    obtain ⟨r', q, rfl, hr'⟩ := S.shapeAt_row (i := i) (x := y) hy
    have he : r = r' := Tuples.map_injective (S.index i) (hr.trans hr'.symm)
    subst r'
    exact ⟨_, S.rowDiff_refl_at i r n s q⟩

omit [Nonempty J] in
theorem colDiff_exists {x y : S.X} {t : Tuple S.I} {b : S.B}
    (hx : S.shape x = .col t b ∅) (hy : S.shape y = .col t b ∅) :
    ∃ v, S.colDiff x y = some v := by
  induction x, y using DirectLimit.induction₂ S.pointMap with
  | ih i x y =>
    obtain ⟨r, c, v, rfl, hr, hc⟩ := S.shapeAt_col (i := i) (x := x) hx
    obtain ⟨r', c', w, rfl, hr', hc'⟩ := S.shapeAt_col (i := i) (x := y) hy
    have he : r = r' := Tuples.map_injective (S.index i) (hr.trans hr'.symm)
    have he' : c = c' := (S.base i).injective (hc.trans hc'.symm)
    subst r'; subst c'
    exact ⟨_, S.colDiff_refl_at i r c v w⟩

omit [Nonempty J] in
@[simp] theorem base_lt (i : J) (a b : (S.obj i).B) :
    S.base i a < S.base i b ↔ a < b := by
  change (S.le (S.base i a) (S.base i b) ∧ ¬ S.le (S.base i b) (S.base i a)) ↔ _
  rw [le_base, le_base, lt_iff_le_not_ge]

instance dense : DenselyOrdered S.B where
  dense := by
    intro a b
    induction a, b using DirectLimit.induction₂ S.baseMap with
    | ih i a b =>
      intro h
      have hab : a < b := (S.base_lt i a b).1 h
      obtain ⟨c, hac, hcb⟩ := exists_between hab
      exact ⟨S.base i c, (S.base_lt i a c).2 hac, (S.base_lt i c b).2 hcb⟩

instance noMin : NoMinOrder S.B where
  exists_lt := by
    intro a
    induction a using DirectLimit.induction S.baseMap with
    | ih i a =>
      obtain ⟨b, hb⟩ := exists_lt a
      exact ⟨S.base i b, (S.base_lt i b a).2 hb⟩

instance noMax : NoMaxOrder S.B where
  exists_gt := by
    intro a
    induction a using DirectLimit.induction S.baseMap with
    | ih i a =>
      obtain ⟨b, hb⟩ := exists_gt a
      exact ⟨S.base i b, (S.base_lt i a b).2 hb⟩

theorem rowOrigin_exists (t : Tuple S.I) (n : ℕ) :
    ∃ x, S.shape x = .row t n ∅ := by
  obtain ⟨i, _, r, hr⟩ := S.tuple_exists t (Classical.arbitrary J)
  exact ⟨S.point i (.row r n ∅), congrArg (fun t => Point.row t n ∅) hr⟩

def rowOrigin (t : Tuple S.I) (n : ℕ) : S.X := (S.rowOrigin_exists t n).choose

@[simp] theorem rowOrigin_shape (t : Tuple S.I) (n : ℕ) :
    S.shape (S.rowOrigin t n) = .row t n ∅ := (S.rowOrigin_exists t n).choose_spec

theorem colOrigin_exists (t : Tuple S.I) (b : S.B) :
    ∃ x, S.shape x = .col t b ∅ := by
  induction b using DirectLimit.induction S.baseMap with
  | ih i b =>
    obtain ⟨j, hij, r, hr⟩ := S.tuple_exists t i
    refine ⟨S.point j (.col r ((S.map i j hij).base b) ∅), ?_⟩
    change Point.col (Tuples.map (S.index j) r) (S.base j ((S.map i j hij).base b)) ∅ = _
    rw [hr, S.base_map]
    rfl

def colOrigin (t : Tuple S.I) (b : S.B) : S.X := (S.colOrigin_exists t b).choose

@[simp] theorem colOrigin_shape (t : Tuple S.I) (b : S.B) :
    S.shape (S.colOrigin t b) = .col t b ∅ := (S.colOrigin_exists t b).choose_spec

theorem row_translate_exists {o : S.X} {t : Tuple S.I} {n : ℕ}
    (ho : S.shape o = .row t n ∅) (s : Finset S.B) :
    ∃ x, S.shape x = .row t n ∅ ∧ S.rowDiff o x = some s := by
  induction o using DirectLimit.induction S.pointMap with
  | ih i o =>
    obtain ⟨r, a, rfl, hr⟩ := S.shapeAt_row (i := i) (x := o) ho
    obtain ⟨j, hij, q, hq⟩ := S.finset_exists s i
    let f := S.map i j hij
    let r' := Tuples.map f.index r
    let a' := f.rowShift r n ∆ a.map f.base.toEmbedding
    refine ⟨S.point j (.row r' n (a' ∆ q)), ?_, ?_⟩
    · change Point.row (Tuples.map (S.index j) r') n ∅ = _
      rw [show Tuples.map (S.index j) r' = t from (S.tuple_map i j hij r).trans hr]
    · change S.rowDiff (S.point i (.row r n a)) (S.point j (.row r' n (a' ∆ q))) = _
      rw [← S.point_map i j hij (.row r n a)]
      change S.rowDiff (S.point j (.row r' n a')) (S.point j (.row r' n (a' ∆ q))) = _
      rw [S.rowDiff_refl_at, symmDiff_symmDiff_cancel_left, hq]

omit [Nonempty J] in
theorem col_translate_exists {o : S.X} {t : Tuple S.I} {b : S.B}
    (ho : S.shape o = .col t b ∅) (v : Finset ℕ) :
    ∃ x, S.shape x = .col t b ∅ ∧ S.colDiff o x = some v := by
  induction o using DirectLimit.induction S.pointMap with
  | ih i o =>
    obtain ⟨r, c, w, rfl, hr, hc⟩ := S.shapeAt_col (i := i) (x := o) ho
    refine ⟨S.point i (.col r c (w ∆ v)), ?_, ?_⟩
    · change Point.col (Tuples.map (S.index i) r) (S.base i c) ∅ = _
      rw [hr, hc]
    · change S.colDiff (S.point i (.col r c w)) (S.point i (.col r c (w ∆ v))) = _
      rw [S.colDiff_refl_at, symmDiff_symmDiff_cancel_left]

def rowPoint (t : Tuple S.I) (n : ℕ) (s : Finset S.B) : S.X :=
  (S.row_translate_exists (S.rowOrigin_shape t n) s).choose

def colPoint (t : Tuple S.I) (b : S.B) (v : Finset ℕ) : S.X :=
  (S.col_translate_exists (S.colOrigin_shape t b) v).choose

@[simp] theorem rowPoint_shape (t : Tuple S.I) (n : ℕ) (s : Finset S.B) :
    S.shape (S.rowPoint t n s) = .row t n ∅ :=
  (S.row_translate_exists (S.rowOrigin_shape t n) s).choose_spec.1

@[simp] theorem rowPoint_diff (t : Tuple S.I) (n : ℕ) (s : Finset S.B) :
    S.rowDiff (S.rowOrigin t n) (S.rowPoint t n s) = some s :=
  (S.row_translate_exists (S.rowOrigin_shape t n) s).choose_spec.2

@[simp] theorem colPoint_shape (t : Tuple S.I) (b : S.B) (v : Finset ℕ) :
    S.shape (S.colPoint t b v) = .col t b ∅ :=
  (S.col_translate_exists (S.colOrigin_shape t b) v).choose_spec.1

@[simp] theorem colPoint_diff (t : Tuple S.I) (b : S.B) (v : Finset ℕ) :
    S.colDiff (S.colOrigin t b) (S.colPoint t b v) = some v :=
  (S.col_translate_exists (S.colOrigin_shape t b) v).choose_spec.2

def bitAt (i : J) : (S.obj i).Carrier → (S.obj i).Carrier → Bool
  | .row t n s, .col r b v => if t = r then Matrix.bit ((S.obj i).bits t) n s b v else false
  | _, _ => false

omit [IsDirectedOrder J] [Nonempty J] in
theorem bitAt_map (i j : J) (h : i ≤ j) (x y : (S.obj i).Carrier) :
    S.bitAt j ((S.map i j h).onPoint x) ((S.map i j h).onPoint y) = S.bitAt i x y := by
  cases x <;> cases y <;> simp only [Map.onPoint, bitAt]
  case row.col t n s r b v =>
    by_cases ht : t = r
    · subst r
      simp only [↓reduceIte]
      exact (S.map i j h).bit_all t n s b v
    · simp only [Tuples.map_eq_iff, ht, ↓reduceIte]

def bit : S.X → S.X → Bool := DirectLimit.lift₂ S.pointMap S.pointMap S.bitAt
  (fun i j h x y => (S.bitAt_map i j h x y).symm)

omit [Nonempty J] in
@[simp] theorem bit_point (i : J) (x y : (S.obj i).Carrier) :
    S.bit (S.point i x) (S.point i y) = S.bitAt i x y := by
  exact DirectLimit.lift₂_def S.pointMap S.pointMap S.bitAt _ i x y

omit [Nonempty J] in
theorem bit_row_change {o x c : S.X} {t : Tuple S.I} {n : ℕ} {b : S.B} {s : Finset S.B}
    (ho : S.shape o = .row t n ∅) (hx : S.shape x = .row t n ∅)
    (hc : S.shape c = .col t b ∅) (hd : S.rowDiff o x = some s) :
    S.bit x c = (S.bit o c ^^ decide (b ∈ s)) := by
  induction o, x, c using DirectLimit.induction₃ S.pointMap with
  | ih i o x c =>
    obtain ⟨r, a, rfl, hr⟩ := S.shapeAt_row (i := i) (x := o) ho
    obtain ⟨r', q, rfl, hr'⟩ := S.shapeAt_row (i := i) (x := x) hx
    obtain ⟨r'', d, v, rfl, hr'', hb⟩ := S.shapeAt_col (i := i) (x := c) hc
    have h1 := Tuples.map_injective (S.index i) (hr'.trans hr.symm)
    have h2 := Tuples.map_injective (S.index i) (hr''.trans hr.symm)
    subst r'; subst r''
    change S.rowDiff (S.point i (.row r n a)) (S.point i (.row r n q)) = some s at hd
    rw [S.rowDiff_refl_at] at hd
    have hs := Option.some.inj hd
    subst s; subst b
    change S.bit (S.point i (.row r n q)) (S.point i (.col r d v)) =
      (S.bit (S.point i (.row r n a)) (S.point i (.col r d v)) ^^ _)
    simp only [bit_point, bitAt, ↓reduceIte, Matrix.bit, FiniteSupports.bit_symmDiff,
      Finset.mem_map, (S.base i).injective.eq_iff, exists_eq_right]
    generalize (S.obj i).bits r n d = z
    generalize decide (d ∈ a) = p
    generalize decide (d ∈ q) = q'
    generalize decide (n ∈ v) = w
    cases z <;> cases p <;> cases q' <;> cases w <;> rfl

omit [Nonempty J] in
theorem bit_col_change {r o x : S.X} {t : Tuple S.I} {n : ℕ} {b : S.B} {v : Finset ℕ}
    (hr : S.shape r = .row t n ∅) (ho : S.shape o = .col t b ∅)
    (hx : S.shape x = .col t b ∅) (hd : S.colDiff o x = some v) :
    S.bit r x = (S.bit r o ^^ decide (n ∈ v)) := by
  induction r, o, x using DirectLimit.induction₃ S.pointMap with
  | ih i r o x =>
    obtain ⟨t', a, rfl, ht⟩ := S.shapeAt_row (i := i) (x := r) hr
    obtain ⟨t'', c, q, rfl, ht', hb⟩ := S.shapeAt_col (i := i) (x := o) ho
    obtain ⟨t''', d, w, rfl, ht'', hb'⟩ := S.shapeAt_col (i := i) (x := x) hx
    have h1 := Tuples.map_injective (S.index i) (ht'.trans ht.symm)
    have h2 := Tuples.map_injective (S.index i) (ht''.trans ht.symm)
    have h3 := (S.base i).injective (hb'.trans hb.symm)
    subst t''; subst t'''; subst d
    change S.colDiff (S.point i (.col t' c q)) (S.point i (.col t' c w)) = some v at hd
    rw [S.colDiff_refl_at] at hd
    have hv := Option.some.inj hd
    subst v
    change S.bit (S.point i (.row t' n a)) (S.point i (.col t' c w)) =
      (S.bit (S.point i (.row t' n a)) (S.point i (.col t' c q)) ^^ _)
    simp only [bit_point, bitAt, ↓reduceIte, Matrix.bit, FiniteSupports.bit_symmDiff]
    generalize (S.obj i).bits t' n c = z
    generalize decide (c ∈ a) = p
    generalize decide (n ∈ q) = q'
    generalize decide (n ∈ w) = w'
    cases z <;> cases p <;> cases q' <;> cases w' <;> rfl

variable (hconv : ∀ i j (h : i ≤ j), Set.OrdConnected (Set.range (S.map i j h).base))

include hconv in
omit [Nonempty J] in
theorem base_convex (i : J) : Set.OrdConnected (Set.range (S.base i)) := by
  constructor
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ c hc
  induction c using DirectLimit.induction S.baseMap with
  | ih j c =>
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    have ha := S.base_map i k hik a
    have hb := S.base_map i k hik b
    have hcc := S.base_map j k hjk c
    change S.base i a ≤ S.base j c ∧ S.base j c ≤ S.base i b at hc
    rw [← ha, ← hb, ← hcc] at hc
    have h : (S.map j k hjk).base c ∈
        Set.Icc ((S.map i k hik).base a) ((S.map i k hik).base b) := by
      exact ⟨(S.le_base k _ _).1 hc.1, (S.le_base k _ _).1 hc.2⟩
    obtain ⟨d, hd⟩ := (hconv i k hik).out ⟨a, rfl⟩ ⟨b, rfl⟩ h
    refine ⟨d, ?_⟩
    change S.base i d = S.base j c
    rw [← S.base_map i k hik d, hd, S.base_map]

omit [Nonempty J] in
include hconv in
theorem locallyCountable (a b : S.B) : (Set.Icc a b).Countable := by
  induction a, b using DirectLimit.induction₂ S.baseMap with
  | ih i a b =>
    have h : Set.Icc (S.base i a) (S.base i b) ⊆
        S.base i '' Set.Icc a b := by
      intro c hc
      obtain ⟨d, rfl⟩ := (S.base_convex hconv i).out ⟨a, rfl⟩ ⟨b, rfl⟩ hc
      exact ⟨d, ⟨(S.le_base i a d).1 hc.1, (S.le_base i d b).1 hc.2⟩, rfl⟩
    exact (((S.obj i).locallyCountable a b).image (S.base i)).mono h

def limitData : Arrays.Data.{u} where
  I := S.I
  B := S.B
  indexNonempty := inferInstance
  baseNonempty := inferInstance
  order := S.order
  dense := S.dense
  noMin := S.noMin
  noMax := S.noMax
  locallyCountable := S.locallyCountable hconv
  bits t n b := S.bit (S.rowOrigin t n) (S.colOrigin t b)

def rowShift (i : J) (t : Tuple (S.obj i).I) (n : ℕ) : Finset S.B :=
  (S.rowDiff_exists (S.rowOrigin_shape (Tuples.map (S.index i) t) n)
    (show S.shape (S.point i (.row t n ∅)) = .row (Tuples.map (S.index i) t) n ∅ from rfl)).choose

def colShift (i : J) (t : Tuple (S.obj i).I) (b : (S.obj i).B) : Finset ℕ :=
  (S.colDiff_exists (S.colOrigin_shape (Tuples.map (S.index i) t) (S.base i b))
    (show S.shape (S.point i (.col t b ∅)) =
      .col (Tuples.map (S.index i) t) (S.base i b) ∅ from rfl)).choose

@[simp] theorem rowShift_spec (i : J) (t : Tuple (S.obj i).I) (n : ℕ) :
    S.rowDiff (S.rowOrigin (Tuples.map (S.index i) t) n) (S.point i (.row t n ∅)) =
      some (S.rowShift i t n) :=
  (S.rowDiff_exists (S.rowOrigin_shape (Tuples.map (S.index i) t) n)
    (show S.shape (S.point i (.row t n ∅)) = .row (Tuples.map (S.index i) t) n ∅ from rfl)).choose_spec

@[simp] theorem colShift_spec (i : J) (t : Tuple (S.obj i).I) (b : (S.obj i).B) :
    S.colDiff (S.colOrigin (Tuples.map (S.index i) t) (S.base i b)) (S.point i (.col t b ∅)) =
      some (S.colShift i t b) :=
  (S.colDiff_exists (S.colOrigin_shape (Tuples.map (S.index i) t) (S.base i b))
    (show S.shape (S.point i (.col t b ∅)) =
      .col (Tuples.map (S.index i) t) (S.base i b) ∅ from rfl)).choose_spec

def toLimit (i : J) : Map (S.obj i) (S.limitData hconv) where
  index := S.index i
  base := S.baseOrder i
  rowShift := S.rowShift i
  colShift := S.colShift i
  bit_agrees t n b := by
    have hr := S.bit_row_change (S.rowOrigin_shape (Tuples.map (S.index i) t) n)
      (show S.shape (S.point i (.row t n ∅)) = _ from rfl)
      (show S.shape (S.point i (.col t b ∅)) = _ from rfl) (S.rowShift_spec i t n)
    have hc := S.bit_col_change (S.rowOrigin_shape (Tuples.map (S.index i) t) n)
      (S.colOrigin_shape (Tuples.map (S.index i) t) (S.base i b))
      (show S.shape (S.point i (.col t b ∅)) = _ from rfl) (S.colShift_spec i t b)
    rw [hc] at hr
    simp only [bit_point, bitAt, ↓reduceIte, Matrix.bit, Finset.notMem_empty,
      decide_false, Bool.xor_false] at hr
    change (S.bit (S.rowOrigin (Tuples.map (S.index i) t) n)
      (S.colOrigin (Tuples.map (S.index i) t) (S.base i b)) ^^
      decide (S.base i b ∈ S.rowShift i t n) ^^ decide (n ∈ S.colShift i t b)) = _
    rw [Bool.xor_right_comm]
    exact hr.symm

theorem rowShift_comp (i j : J) (h : i ≤ j) (t : Tuple (S.obj i).I) (n : ℕ) :
    S.rowShift j (Tuples.map (S.map i j h).index t) n ∆
      ((S.map i j h).rowShift t n).map (S.base j) = S.rowShift i t n := by
  let f := S.map i j h
  have hd := S.rowDiff_refl_at j (Tuples.map f.index t) n ∅ (f.rowShift t n)
  simp only [← Finset.bot_eq_empty, bot_symmDiff] at hd
  have he := S.rowDiff_trans (S.rowShift_spec j (Tuples.map f.index t) n) hd
  have hp : S.point j (.row (Tuples.map f.index t) n (f.rowShift t n)) =
      S.point i (.row t n ∅) := by
    have hp := S.point_map i j h (.row t n ∅)
    simp only [Map.onPoint, Finset.map_empty] at hp
    simpa only [f, ← Finset.bot_eq_empty, symmDiff_bot] using hp
  rw [hp, show Tuples.map (S.index j) (Tuples.map f.index t) = Tuples.map (S.index i) t from
    S.tuple_map i j h t, S.rowShift_spec] at he
  exact (Option.some.inj he).symm

theorem colShift_comp (i j : J) (h : i ≤ j) (t : Tuple (S.obj i).I) (b : (S.obj i).B) :
    S.colShift j (Tuples.map (S.map i j h).index t) ((S.map i j h).base b) ∆
      (S.map i j h).colShift t b = S.colShift i t b := by
  let f := S.map i j h
  have hd := S.colDiff_refl_at j (Tuples.map f.index t) (f.base b) ∅ (f.colShift t b)
  simp only [← Finset.bot_eq_empty, bot_symmDiff] at hd
  have he := S.colDiff_trans (S.colShift_spec j (Tuples.map f.index t) (f.base b)) hd
  have hp : S.point j (.col (Tuples.map f.index t) (f.base b) (f.colShift t b)) =
      S.point i (.col t b ∅) := by
    have hp := S.point_map i j h (.col t b ∅)
    simp only [Map.onPoint] at hp
    simpa only [f, ← Finset.bot_eq_empty, symmDiff_bot] using hp
  rw [hp, show Tuples.map (S.index j) (Tuples.map f.index t) = Tuples.map (S.index i) t from
    S.tuple_map i j h t, show S.base j (f.base b) = S.base i b from S.base_map i j h b,
    S.colShift_spec] at he
  exact (Option.some.inj he).symm

theorem toLimit_comp (i j : J) (h : i ≤ j) :
    (S.toLimit hconv j).comp (S.map i j h) = S.toLimit hconv i := by
  apply Map.ext_onPoint
  intro x
  rw [Map.comp_onPoint]
  cases x with
  | index a =>
    change Point.index (S.index j ((S.map i j h).index a)) = Point.index (S.index i a)
    rw [S.index_map]
  | base b =>
    change Point.base (S.base j ((S.map i j h).base b)) = Point.base (S.base i b)
    rw [S.base_map]
  | group s =>
    change Point.group ((s.map (S.map i j h).base.toEmbedding).map (S.base j)) =
      Point.group (s.map (S.base i))
    rw [S.finset_map]
  | star v => rfl
  | row t n s =>
    change Point.row (Tuples.map (S.index j) (Tuples.map (S.map i j h).index t)) n
      (S.rowShift j (Tuples.map (S.map i j h).index t) n ∆
        ((S.map i j h).rowShift t n ∆ s.map (S.map i j h).base.toEmbedding).map (S.base j)) =
      Point.row (Tuples.map (S.index i) t) n (S.rowShift i t n ∆ s.map (S.base i))
    rw [S.tuple_map, FiniteSupports.map_symmDiff, ← symmDiff_assoc, S.rowShift_comp, S.finset_map]
  | col t b v =>
    change Point.col (Tuples.map (S.index j) (Tuples.map (S.map i j h).index t))
      (S.base j ((S.map i j h).base b))
      (S.colShift j (Tuples.map (S.map i j h).index t) ((S.map i j h).base b) ∆
        ((S.map i j h).colShift t b ∆ v)) =
      Point.col (Tuples.map (S.index i) t) (S.base i b) (S.colShift i t b ∆ v)
    rw [S.tuple_map, S.base_map, ← symmDiff_assoc, S.colShift_comp]

theorem toLimit_covers (x : (S.limitData hconv).Carrier) :
    ∃ i y, (S.toLimit hconv i).onPoint y = x := by
  change Point S.I S.B at x
  cases x with
  | index a =>
    induction a using DirectLimit.induction S.indexMap with
    | ih i a => exact ⟨i, .index a, rfl⟩
  | base b =>
    induction b using DirectLimit.induction S.baseMap with
    | ih i b => exact ⟨i, .base b, rfl⟩
  | group s =>
    obtain ⟨i, _, r, hr⟩ := S.finset_exists s (Classical.arbitrary J)
    exact ⟨i, .group r, congrArg Point.group hr⟩
  | star v => exact ⟨Classical.arbitrary J, .star v, rfl⟩
  | row t n s =>
    obtain ⟨⟨i, x⟩, hx⟩ := Quotient.exists_rep (S.rowPoint t n s)
    change S.point i x = S.rowPoint t n s at hx
    have hshape : S.shapeAt i x = .row t n ∅ := by rw [← S.shape_point, hx, S.rowPoint_shape]
    obtain ⟨r, a, rfl, hr⟩ := S.shapeAt_row hshape
    have hd := S.rowDiff_trans (S.rowShift_spec i r n) (S.rowDiff_refl_at i r n ∅ a)
    simp only [← Finset.bot_eq_empty, bot_symmDiff] at hd
    rw [hr, hx, S.rowPoint_diff] at hd
    refine ⟨i, .row r n a, ?_⟩
    change Point.row (Tuples.map (S.index i) r) n
      (S.rowShift i r n ∆ a.map (S.base i)) = .row t n s
    rw [hr, ← Option.some.inj hd]
  | col t b v =>
    obtain ⟨⟨i, x⟩, hx⟩ := Quotient.exists_rep (S.colPoint t b v)
    change S.point i x = S.colPoint t b v at hx
    have hshape : S.shapeAt i x = .col t b ∅ := by rw [← S.shape_point, hx, S.colPoint_shape]
    obtain ⟨r, c, a, rfl, hr, hc⟩ := S.shapeAt_col hshape
    have hd := S.colDiff_trans (S.colShift_spec i r c) (S.colDiff_refl_at i r c ∅ a)
    simp only [← Finset.bot_eq_empty, bot_symmDiff] at hd
    rw [hr, hc, hx, S.colPoint_diff] at hd
    refine ⟨i, .col r c a, ?_⟩
    change Point.col (Tuples.map (S.index i) r) (S.base i c) (S.colShift i r c ∆ a) = .col t b v
    rw [hr, hc, ← Option.some.inj hd]

def underlying : S.X → (S.limitData hconv).Carrier :=
  DirectLimit.lift S.pointMap (fun i => (S.toLimit hconv i).onPoint) (by
    intro i j h x
    simpa only [pointMap, Map.toEmbedding, Function.Embedding.coeFn_mk, Map.comp_onPoint] using
      (congrArg (fun f : Map _ _ => f.onPoint x) (S.toLimit_comp hconv i j h)).symm)

@[simp] theorem underlying_point (i : J) (x : (S.obj i).Carrier) :
    S.underlying hconv (S.point i x) = (S.toLimit hconv i).onPoint x := rfl

theorem underlying_bijective : Function.Bijective (S.underlying hconv) := by
  constructor
  · intro x y
    induction x, y using DirectLimit.induction₂ S.pointMap with
    | ih i x y =>
      intro h
      exact congrArg (S.point i) ((S.toLimit hconv i).injective h)
  · intro x
    obtain ⟨i, y, hy⟩ := S.toLimit_covers hconv x
    exact ⟨S.point i y, hy⟩

def equivalence : S.X ≃ (S.limitData hconv).Carrier :=
  Equiv.ofBijective (S.underlying hconv) (S.underlying_bijective hconv)

@[simp] theorem equivalence_point (i : J) (x : (S.obj i).Carrier) :
    S.equivalence hconv (S.point i x) = (S.toLimit hconv i).onPoint x := rfl

@[simp] theorem equivalence_symm_stage (i : J) (x : (S.obj i).Carrier) :
    (S.equivalence hconv).symm ((S.toLimit hconv i).onPoint x) = S.point i x :=
  (S.equivalence hconv).symm_apply_apply (S.point i x)

theorem common_points {A : Type v} [Finite A] (x : A → (S.limitData hconv).Carrier) (i : J) :
    ∃ j, i ≤ j ∧ ∃ y : A → (S.obj j).Carrier, ∀ a, (S.toLimit hconv j).onPoint (y a) = x a := by
  obtain ⟨j, hij, y, hy⟩ := LimitTools.common S.pointMap
    (fun a b h => (S.map a b h).injective) (fun a => (S.equivalence hconv).symm (x a)) i
  refine ⟨j, hij, y, fun a => ?_⟩
  exact (congrArg (S.equivalence hconv) (hy a)).trans ((S.equivalence hconv).apply_symm_apply (x a))

variable {hCH : CH.{u}}

theorem toLimit_strong
    (hstrong : ∀ i j h, (S.map i j h).Strong hCH) (i : J) :
    (S.toLimit hconv i).Strong hCH := by
  constructor
  · exact S.base_convex hconv i
  · intro t b hb
    induction b using DirectLimit.induction S.baseMap with
    | ih j b =>
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      let c := (S.map j k hjk).base b
      have hc : c ∉ Set.range (S.map i k hik).base := by
        rintro ⟨a, ha⟩
        apply hb
        refine ⟨a, ?_⟩
        change S.base i a = S.base j b
        rw [← S.base_map i k hik a, ha, S.base_map]
      have ht := (hstrong i k hik).outside t c hc
      have he : ∀ r : Tuple (S.obj i).I,
          (S.toLimit hconv i).colors r (S.base j b) = (S.map i k hik).colors r c := by
        intro r
        rw [← S.toLimit_comp hconv i k hik, ← S.base_map j k hjk b]
        exact Map.comp_colors_base _ _ r c
      change Tests.Test hCH (fun r => (S.toLimit hconv i).colors r (S.base j b)) t
      simpa only [he] using ht

theorem limit_object (hobj : ∀ i, (S.obj i).IsObject hCH)
    (hstrong : ∀ i j h, (S.map i j h).Strong hCH) :
    (S.limitData hconv).IsObject hCH := by
  intro t
  obtain ⟨i, _, r, hr⟩ := S.tuple_exists t (Classical.arbitrary J)
  let f := S.toLimit hconv i
  have hf : f.Strong hCH := S.toLimit_strong hconv hstrong i
  have hbad := ((hobj i r).image f.base).union (f.exceptions_countable r)
  apply hbad.mono
  intro b hb
  by_cases hex : b ∈ f.exceptions r
  · exact Or.inr hex
  · left
    have ht : ¬ Tests.Test hCH (fun s => f.colors s b) r := by
      intro h
      apply hb
      have he := (f.test_away hCH r b hex).1 h
      change Tests.Test hCH (fun s => (S.limitData hconv).colors s b) (Tuples.map (S.index i) r) at he
      exact hr ▸ he
    by_cases hbase : b ∈ Set.range f.base
    · obtain ⟨c, rfl⟩ := hbase
      exact ⟨c, by simpa only [Set.mem_ofPred_eq, Map.colors_base] using ht, rfl⟩
    · exact (ht (hf.outside r b hbase)).elim

variable {N : Arrays.Data.{u}} (q : ∀ i, Map (S.obj i) N)
  (hq : ∀ i j h, (q j).comp (S.map i j h) = q i)

def liftPoint : S.X → N.Carrier := DirectLimit.lift S.pointMap (fun i => (q i).onPoint)
  (fun i j h x => by
    simpa only [pointMap, Map.toEmbedding, Function.Embedding.coeFn_mk, Map.comp_onPoint] using (congrArg (fun f : Map _ _ => f.onPoint x) (hq i j h)).symm)

omit [Nonempty J] in
@[simp] theorem liftPoint_point (i : J) (x : (S.obj i).Carrier) :
    S.liftPoint q hq (S.point i x) = (q i).onPoint x := rfl

omit [Nonempty J] in
theorem liftPoint_injective : Function.Injective (S.liftPoint q hq) := by
  intro x y
  induction x, y using DirectLimit.induction₂ S.pointMap with
  | ih i x y =>
    intro h
    exact congrArg (S.point i) ((q i).injective h)

def liftFunction (x : (S.limitData hconv).Carrier) : N.Carrier :=
  S.liftPoint q hq ((S.equivalence hconv).symm x)

@[simp] theorem liftFunction_stage (i : J) (x : (S.obj i).Carrier) :
    S.liftFunction hconv q hq ((S.toLimit hconv i).onPoint x) = (q i).onPoint x := by
  rw [liftFunction, equivalence_symm_stage, liftPoint_point]

theorem liftFunction_injective : Function.Injective (S.liftFunction hconv q hq) :=
  (S.liftPoint_injective q hq).comp (S.equivalence hconv).symm.injective

def liftRaw : RawEmbedding (S.limitData hconv) N where
  toEmbedding := ⟨S.liftFunction hconv q hq, S.liftFunction_injective hconv q hq⟩
  relates s xs := by
    obtain ⟨i, _, y, hy⟩ := S.common_points hconv (fun a : Fin xs.length => xs.get a) (Classical.arbitrary J)
    have he : (List.ofFn y).map (S.toLimit hconv i).onPoint = xs := by
      rw [List.map_ofFn]
      have hfun : (fun a => (S.toLimit hconv i).onPoint (y a)) = xs.get := funext hy
      change List.ofFn (fun a => (S.toLimit hconv i).onPoint (y a)) = xs
      rw [hfun, List.ofFn_get]
    rw [← he, List.map_map]
    have he' : (fun a => S.liftFunction hconv q hq ((S.toLimit hconv i).onPoint a)) =
        (q i).onPoint := funext (S.liftFunction_stage hconv q hq i)
    change N.rawRel s ((List.ofFn y).map (fun a => S.liftFunction hconv q hq
      ((S.toLimit hconv i).onPoint a))) ↔ _
    rw [he', (q i).rawRel, (S.toLimit hconv i).rawRel]
  supports s b := by
    obtain ⟨i, _, r, hr⟩ := S.finset_exists s (Classical.arbitrary J)
    subst s
    have hg : S.liftFunction hconv q hq (.group (r.map (S.base i))) =
        .group (r.map (q i).base.toEmbedding) := S.liftFunction_stage hconv q hq i (.group r)
    have hb (a : (S.obj i).B) : S.liftFunction hconv q hq (.base (S.base i a)) =
        .base ((q i).base a) := S.liftFunction_stage hconv q hq i (.base a)
    change N.rawRel .incidence [.base b, S.liftFunction hconv q hq (.group (r.map (S.base i)))] ↔ _
    rw [hg]
    change b ∈ r.map (q i).base.toEmbedding ↔
      ∃ c ∈ r.map (S.base i), S.liftFunction hconv q hq (.base c) = .base b
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨a, ha, hab⟩
      refine ⟨S.base i a, ⟨a, ha, rfl⟩, ?_⟩
      rw [hb]
      exact congrArg Point.base hab
    · rintro ⟨c, ⟨a, ha, rfl⟩, he⟩
      exact ⟨a, ha, Point.base.inj ((hb a).symm.trans he)⟩

def liftMap : Map (S.limitData hconv) N := (S.liftRaw hconv q hq).toMap

@[simp] theorem liftMap_stage (i : J) (x : (S.obj i).Carrier) :
    (S.liftMap hconv q hq).onPoint ((S.toLimit hconv i).onPoint x) = (q i).onPoint x := by
  rw [liftMap, RawEmbedding.toMap_onPoint]
  exact S.liftFunction_stage hconv q hq i x

@[simp] theorem liftMap_comp (i : J) :
    (S.liftMap hconv q hq).comp (S.toLimit hconv i) = q i := by
  apply Map.ext_onPoint
  intro x
  rw [Map.comp_onPoint, S.liftMap_stage]

include hq in

theorem liftMap_strong (hs : ∀ i, (q i).Strong hCH) :
    (S.liftMap hconv q hq).Strong hCH := by
  let g := S.liftMap hconv q hq
  have hbase (i : J) (a : (S.obj i).B) : g.base (S.base i a) = (q i).base a :=
    congrArg (fun f : Map _ _ => f.base a) (S.liftMap_comp hconv q hq i)
  constructor
  · constructor
    rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩ b hb
    induction a, c using DirectLimit.induction₂ S.baseMap with
    | ih i a c =>
      change g.base (S.base i a) ≤ b ∧ b ≤ g.base (S.base i c) at hb
      rw [hbase, hbase] at hb
      obtain ⟨d, hd⟩ := (hs i).convex.out ⟨a, rfl⟩ ⟨c, rfl⟩ hb
      exact ⟨S.base i d, (hbase i d).trans hd⟩
  · intro t b hb
    obtain ⟨i, _, r, hr⟩ := S.tuple_exists t (Classical.arbitrary J)
    have hb' : b ∉ Set.range (q i).base := by
      rintro ⟨a, ha⟩
      exact hb ⟨S.base i a, (hbase i a).trans ha⟩
    have ht := (hs i).outside r b hb'
    have he (s : Tuple (S.obj i).I) :
        (q i).colors s b = g.colors (Tuples.map (S.index i) s) b := by
      rw [← S.liftMap_comp hconv q hq i]
      exact Map.comp_colors_outside g (S.toLimit hconv i) s b hb
    rw [← hr]
    change Tests.Test hCH (fun s : Tuple S.I => g.colors s b) (Tuples.map (S.index i) r)
    apply (Tests.map hCH (S.index i) (fun s : Tuple S.I => g.colors s b) r).2
    exact (Tests.congr hCH r (fun m e => he (Tuples.sub r e))).1 ht

end Data
end System
end Arrays

end CHObstruction

end

end OAI
