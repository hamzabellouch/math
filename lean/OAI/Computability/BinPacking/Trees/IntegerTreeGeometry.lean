import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Infix
import Mathlib.Order.Interval.Set.Basic
import OAI.Computability.BinPacking.Machines.IntegerPackingArithmetic

namespace OAI

namespace BinPackingGap

structure UniformTree where
  height : ℕ
  leaves : Finset (List ℕ)
  leaves_nonempty : leaves.Nonempty
  length_leaf : ∀ l ∈ leaves, l.length = height
  positive_labels : ∀ l ∈ leaves, ∀ a ∈ l, 0 < a

namespace UniformTree

def prefixes (l : List ℕ) : Finset (List ℕ) :=
  (Finset.range (l.length + 1)).image (fun k => l.take k)

@[simp] theorem mem_prefixes_iff {w l : List ℕ} :
    w ∈ prefixes l ↔ w.IsPrefix l := by
  constructor
  · intro hw
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hw
    exact List.take_prefix k l
  · intro h
    exact Finset.mem_image.mpr
      ⟨w.length, Finset.mem_range.mpr (Nat.lt_succ_of_le h.length_le),
        (List.prefix_iff_eq_take.mp h).symm⟩

def vertices (T : UniformTree) : Finset (List ℕ) :=
  T.leaves.biUnion prefixes

theorem mem_vertices_iff (T : UniformTree) {w : List ℕ} :
    w ∈ T.vertices ↔ ∃ l ∈ T.leaves, w.IsPrefix l := by
  simp only [vertices, Finset.mem_biUnion, mem_prefixes_iff]

theorem leaf_mem_vertices (T : UniformTree) {l : List ℕ} (hl : l ∈ T.leaves) :
    l ∈ T.vertices :=
  (T.mem_vertices_iff).mpr ⟨l, hl, List.prefix_refl l⟩

theorem nil_mem_vertices (T : UniformTree) : [] ∈ T.vertices := by
  obtain ⟨l, hl⟩ := T.leaves_nonempty
  exact (T.mem_vertices_iff).mpr ⟨l, hl, List.nil_prefix⟩

theorem vertices_nonempty (T : UniformTree) : T.vertices.Nonempty :=
  ⟨[], T.nil_mem_vertices⟩

theorem prefix_mem_vertices (T : UniformTree) {u v : List ℕ}
    (hv : v ∈ T.vertices) (h : u.IsPrefix v) : u ∈ T.vertices := by
  obtain ⟨l, hl, hvl⟩ := T.mem_vertices_iff.mp hv
  exact T.mem_vertices_iff.mpr ⟨l, hl, h.trans hvl⟩

theorem take_mem_vertices (T : UniformTree) {w : List ℕ}
    (hw : w ∈ T.vertices) (k : ℕ) : w.take k ∈ T.vertices :=
  T.prefix_mem_vertices hw (List.take_prefix k w)

theorem length_le_height (T : UniformTree) {w : List ℕ}
    (hw : w ∈ T.vertices) : w.length ≤ T.height := by
  obtain ⟨l, hl, h⟩ := T.mem_vertices_iff.mp hw
  exact (T.length_leaf l hl) ▸ h.length_le

theorem mem_leaves_iff_length_eq_height (T : UniformTree) {w : List ℕ}
    (hw : w ∈ T.vertices) : w ∈ T.leaves ↔ w.length = T.height := by
  constructor
  · exact T.length_leaf w
  · intro hlen
    obtain ⟨l, hl, h⟩ := T.mem_vertices_iff.mp hw
    have heq : w = l := h.eq_of_length (hlen.trans (T.length_leaf l hl).symm)
    simpa only [heq] using hl

abbrev Node (T : UniformTree) := {w : List ℕ // w ∈ T.vertices}

instance nodeFintype (T : UniformTree) : Fintype T.Node :=
  Finset.fintypeCoeSort T.vertices

def root (T : UniformTree) : T.Node := ⟨[], T.nil_mem_vertices⟩

instance nodeNonempty (T : UniformTree) : Nonempty T.Node := ⟨T.root⟩

@[simp] theorem root_val (T : UniformTree) : T.root.val = [] := rfl

@[simp] theorem node_card (T : UniformTree) :
    Fintype.card T.Node = T.vertices.card := Fintype.card_coe T.vertices

theorem node_card_pos (T : UniformTree) : 0 < Fintype.card T.Node :=
  Fintype.card_pos

def depth {T : UniformTree} (v : T.Node) : ℕ := v.val.length

def ancestor {T : UniformTree} (u v : T.Node) : Prop := u.val.IsPrefix v.val

def leaf {T : UniformTree} (v : T.Node) : Prop := v.val ∈ T.leaves

def child {T : UniformTree} (u v : T.Node) : Prop :=
  ∃ a : ℕ, v.val = u.val ++ [a]

@[simp] theorem depth_root (T : UniformTree) : depth T.root = 0 := rfl

theorem depth_le_height {T : UniformTree} (v : T.Node) : depth v ≤ T.height :=
  T.length_le_height v.property

theorem leaf_iff_depth_eq_height {T : UniformTree} (v : T.Node) :
    leaf v ↔ depth v = T.height :=
  T.mem_leaves_iff_length_eq_height v.property

@[simp] theorem ancestor_refl {T : UniformTree} (v : T.Node) : ancestor v v :=
  List.prefix_refl v.val

theorem ancestor_trans {T : UniformTree} {u v w : T.Node}
    (huv : ancestor u v) (hvw : ancestor v w) : ancestor u w := huv.trans hvw

theorem ancestor_depth_le {T : UniformTree} {u v : T.Node}
    (h : ancestor u v) : depth u ≤ depth v := h.length_le

theorem eq_of_ancestor_of_depth_eq {T : UniformTree} {u v : T.Node}
    (h : ancestor u v) (hlen : depth u = depth v) : u = v :=
  Subtype.ext (h.eq_of_length hlen)

@[simp] theorem root_ancestor {T : UniformTree} (v : T.Node) : ancestor T.root v :=
  List.nil_prefix

theorem eq_root_iff_depth_eq_zero {T : UniformTree} (v : T.Node) :
    v = T.root ↔ depth v = 0 := by
  constructor
  · rintro rfl
    rfl
  · intro h
    apply Subtype.ext
    exact List.length_eq_zero_iff.mp h

def ancestorAt {T : UniformTree} (v : T.Node) (k : ℕ) : T.Node :=
  ⟨v.val.take k, T.take_mem_vertices v.property k⟩

@[simp] theorem ancestorAt_val {T : UniformTree} (v : T.Node) (k : ℕ) :
    (ancestorAt v k).val = v.val.take k := rfl

theorem ancestorAt_ancestor {T : UniformTree} (v : T.Node) (k : ℕ) :
    ancestor (ancestorAt v k) v := List.take_prefix k v.val

theorem depth_ancestorAt {T : UniformTree} (v : T.Node) {k : ℕ}
    (hk : k ≤ depth v) : depth (ancestorAt v k) = k := by
  exact List.length_take_of_le hk

theorem ancestor_eq_ancestorAt {T : UniformTree} {u v : T.Node}
    (h : ancestor u v) : u = ancestorAt v (depth u) :=
  Subtype.ext (List.prefix_iff_eq_take.mp h)

def branchBound (T : UniformTree) : ℕ :=
  max 1 (T.leaves.sup (fun l => l.toFinset.sup id))

theorem one_le_branchBound (T : UniformTree) : 1 ≤ T.branchBound :=
  le_max_left _ _

theorem branchBound_pos (T : UniformTree) : 0 < T.branchBound :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one T.one_le_branchBound

theorem label_pos {T : UniformTree} (v : T.Node) {a : ℕ} (ha : a ∈ v.val) :
    0 < a := by
  obtain ⟨l, hl, h⟩ := T.mem_vertices_iff.mp v.property
  exact T.positive_labels l hl a (h.subset ha)

theorem label_le_branchBound {T : UniformTree} (v : T.Node) {a : ℕ}
    (ha : a ∈ v.val) : a ≤ T.branchBound := by
  obtain ⟨l, hl, h⟩ := T.mem_vertices_iff.mp v.property
  calc
    a ≤ l.toFinset.sup id :=
      Finset.le_sup (f := id) (List.mem_toFinset.mpr (h.subset ha))
    _ ≤ T.leaves.sup (fun l => l.toFinset.sup id) :=
      Finset.le_sup (f := fun l : List ℕ => l.toFinset.sup id) hl
    _ ≤ T.branchBound := le_max_right _ _

theorem exists_child_word {T : UniformTree} (v : T.Node) (hv : depth v < T.height) :
    ∃ a : ℕ, v.val ++ [a] ∈ T.vertices := by
  obtain ⟨l, hl, tail, htail⟩ := T.mem_vertices_iff.mp v.property
  cases tail with
  | nil =>
    have heq : v.val = l := by simpa using htail
    have hlen : depth v = T.height := by
      change v.val.length = T.height
      rw [heq, T.length_leaf l hl]
    exact (Nat.ne_of_lt hv hlen).elim
  | cons a tail =>
    refine ⟨a, T.mem_vertices_iff.mpr ⟨l, hl, tail, ?_⟩⟩
    simpa [List.append_assoc] using htail

theorem exists_child {T : UniformTree} (v : T.Node) (hv : depth v < T.height) :
    ∃ u : T.Node, child v u := by
  obtain ⟨a, ha⟩ := exists_child_word v hv
  exact ⟨⟨v.val ++ [a], ha⟩, a, rfl⟩

theorem child_depth {T : UniformTree} {u v : T.Node} (h : child u v) :
    depth v = depth u + 1 := by
  obtain ⟨a, ha⟩ := h
  simp only [depth, ha, List.length_append, List.length_singleton]

theorem child_ancestor {T : UniformTree} {u v : T.Node} (h : child u v) :
    ancestor u v := by
  obtain ⟨a, ha⟩ := h
  exact ⟨[a], ha.symm⟩

theorem child_label_bounds {T : UniformTree} {u v : T.Node} {a : ℕ}
    (h : v.val = u.val ++ [a]) : 0 < a ∧ a ≤ T.branchBound := by
  have ha : a ∈ v.val := by simp [h]
  exact ⟨label_pos v ha, label_le_branchBound v ha⟩

theorem leaf_iff_no_child {T : UniformTree} (v : T.Node) :
    leaf v ↔ ¬ ∃ u : T.Node, child v u := by
  constructor
  · intro hv ⟨u, hu⟩
    have heq := (leaf_iff_depth_eq_height v).mp hv
    have hle := depth_le_height u
    have hdepth := child_depth hu
    omega
  · intro h
    apply (leaf_iff_depth_eq_height v).mpr
    have hle := depth_le_height v
    by_contra hne
    exact h (exists_child v (lt_of_le_of_ne hle hne))

end UniformTree

def levelCount (marks : Finset (List ℕ)) (depth : ℕ) : ℕ :=
  (marks.filter (fun w => w.length = depth)).card

def colorCount (marks : Finset (List ℕ)) (leaf : List ℕ) : ℕ :=
  (marks.filter (fun w => w.IsPrefix leaf)).card

theorem colorCount_eq_card_inter_prefixes (marks : Finset (List ℕ))
    (leaf : List ℕ) :
    colorCount marks leaf = (marks ∩ UniformTree.prefixes leaf).card := by
  unfold colorCount
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_inter,
    UniformTree.mem_prefixes_iff]

def RespectsTreeQuota (T : UniformTree) (quota : ℕ → ℕ)
    (marks : Finset (List ℕ)) : Prop :=
  [] ∉ marks ∧ ∀ depth, 1 ≤ depth → depth ≤ T.height →
    levelCount marks depth ≤ quota depth

structure AuxiliaryTree (phases : ℕ) where
  tree : UniformTree
  quota : ℕ → ℕ
  quota_pos : ∀ depth, 1 ≤ depth → depth ≤ tree.height → 0 < quota depth
  red : Finset (List ℕ)
  blue : Finset (List ℕ)
  red_subset : red ⊆ tree.vertices
  blue_subset : blue ⊆ tree.vertices
  root_not_red : [] ∉ red
  root_not_blue : [] ∉ blue
  red_blue_disjoint : Disjoint red blue
  red_level : ∀ depth, 1 ≤ depth → depth ≤ tree.height →
    levelCount red depth ≤ quota depth
  blue_level : ∀ depth, 1 ≤ depth → depth ≤ tree.height →
    levelCount blue depth ≤ quota depth
  total_count : ∀ leaf ∈ tree.leaves,
    colorCount red leaf + colorCount blue leaf = phases
  red_witness : ∃ leaf ∈ tree.leaves, colorCount red leaf = phases
  blue_witness : ∃ leaf ∈ tree.leaves, colorCount blue leaf = phases

  avoids : ∀ marks : Finset (List ℕ),
    RespectsTreeQuota tree quota marks →
    ∃ leaf ∈ tree.leaves, Disjoint marks (UniformTree.prefixes leaf)

theorem card_hit_le {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (A : Finset α) (P : ι → Finset α)
    (hP : (I : Set ι).PairwiseDisjoint P) :
    (I.filter (fun i => ¬ Disjoint A (P i))).card ≤ A.card := by
  classical
  let hit := I.filter (fun i => ¬ Disjoint A (P i))
  have hx (i : {i // i ∈ hit}) : ∃ x : {x // x ∈ A}, x.val ∈ P i.val := by
    obtain ⟨x, hxA, hxP⟩ :=
      Finset.not_disjoint_iff.mp (Finset.mem_filter.mp i.property).2
    exact ⟨⟨x, hxA⟩, hxP⟩
  let f (i : {i // i ∈ hit}) : {x // x ∈ A} := (hx i).choose
  have hf (i : {i // i ∈ hit}) : (f i).val ∈ P i.val := (hx i).choose_spec
  have hinj : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    apply Finset.disjoint_left.mp
      (hP (Finset.mem_filter.mp i.property).1
        (Finset.mem_filter.mp j.property).1 hne) (hf i)
    rw [hij]
    exact hf j
  simpa only [Fintype.card_coe, hit] using Fintype.card_le_of_injective f hinj

theorem exists_disjoint_of_card_lt {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (A : Finset α) (P : ι → Finset α)
    (hP : (I : Set ι).PairwiseDisjoint P) (hcard : A.card < I.card) :
    ∃ i ∈ I, Disjoint A (P i) := by
  classical
  by_contra h
  have hhit : ∀ i ∈ I, ¬ Disjoint A (P i) := fun i hi hd => h ⟨i, hi, hd⟩
  have hfilter : I.filter (fun i => ¬ Disjoint A (P i)) = I :=
    Finset.filter_eq_self.mpr hhit
  have hle := card_hit_le I A P hP
  rw [hfilter] at hle
  exact (Nat.not_le_of_lt hcard) hle

def prefixesAfter (stem word : List ℕ) : Finset (List ℕ) :=
  ((UniformTree.prefixes word).erase []).image (fun v => stem ++ v)

@[simp]
theorem mem_prefixesAfter_iff {stem word w : List ℕ} :
    w ∈ prefixesAfter stem word ↔
      ∃ v, v ≠ [] ∧ v.IsPrefix word ∧ stem ++ v = w := by
  simp [prefixesAfter, Finset.mem_image, and_assoc]

theorem stem_not_mem_prefixesAfter (stem word : List ℕ) :
    stem ∉ prefixesAfter stem word := by
  intro h
  obtain ⟨v, hv, _, heq⟩ := mem_prefixesAfter_iff.mp h
  apply hv
  apply List.append_cancel_left (as := stem)
  simpa only [List.append_nil] using heq

theorem prefixes_append_eq (stem word : List ℕ) :
    UniformTree.prefixes (stem ++ word) =
      UniformTree.prefixes stem ∪ prefixesAfter stem word := by
  ext w
  simp only [Finset.mem_union, UniformTree.mem_prefixes_iff]
  constructor
  · intro hw
    rcases List.prefix_or_prefix_of_prefix hw (List.prefix_append stem word) with h | h
    · exact Or.inl h
    · obtain ⟨v, rfl⟩ := h
      by_cases hv : v = []
      · subst v
        exact Or.inl (by simpa only [List.append_nil] using List.prefix_refl stem)
      · exact Or.inr (mem_prefixesAfter_iff.mpr
          ⟨v, hv, (List.prefix_append_right_inj stem).mp hw, rfl⟩)
  · rintro (hw | hw)
    · exact hw.trans (List.prefix_append stem word)
    · obtain ⟨v, _, hv, rfl⟩ := mem_prefixesAfter_iff.mp hw
      exact (List.prefix_append_right_inj stem).mpr hv

theorem disjoint_positive_prefixes_cons {a b : ℕ} (u v : List ℕ) (hab : a ≠ b) :
    Disjoint ((UniformTree.prefixes (a :: u)).erase [])
      ((UniformTree.prefixes (b :: v)).erase []) := by
  apply Finset.disjoint_left.mpr
  intro w hwa hwb
  have hpa := UniformTree.mem_prefixes_iff.mp (Finset.mem_erase.mp hwa).2
  have hpb := UniformTree.mem_prefixes_iff.mp (Finset.mem_erase.mp hwb).2
  cases w with
  | nil => exact (Finset.mem_erase.mp hwa).1 rfl
  | cons x xs =>
      exact hab ((List.cons_prefix_cons.mp hpa).1.symm.trans
        (List.cons_prefix_cons.mp hpb).1)

theorem disjoint_prefixesAfter_cons (stem : List ℕ) {a b : ℕ}
    (u v : List ℕ) (hab : a ≠ b) :
    Disjoint (prefixesAfter stem (a :: u)) (prefixesAfter stem (b :: v)) := by
  apply Finset.disjoint_left.mpr
  intro w hwa hwb
  obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hwa
  obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.mp hwb
  have hxy : x = y := List.append_cancel_left (hxeq.trans hyeq.symm)
  exact Finset.disjoint_left.mp (disjoint_positive_prefixes_cons u v hab)
    hx (hxy.symm ▸ hy)

theorem disjoint_positive_spine_prefixes {a b n m : ℕ} (hab : a ≠ b) :
    Disjoint ((UniformTree.prefixes ((a + 1) :: List.replicate n 1)).erase [])
      ((UniformTree.prefixes ((b + 1) :: List.replicate m 1)).erase []) := by
  apply disjoint_positive_prefixes_cons
  exact fun h => hab (Nat.add_right_cancel h)

theorem disjoint_spine_prefixesAfter (stem : List ℕ) {a b n m : ℕ} (hab : a ≠ b) :
    Disjoint (prefixesAfter stem ((a + 1) :: List.replicate n 1))
      (prefixesAfter stem ((b + 1) :: List.replicate m 1)) := by
  apply disjoint_prefixesAfter_cons
  exact fun h => hab (Nat.add_right_cancel h)

end BinPackingGap

namespace BinPackingGap.TreeGeometry

open _root_.OAI.BinPackingGap.Geometry UniformTree

inductive Side where
  | plus
  | minus
  deriving DecidableEq

instance : Fintype Side where
  elems := {.plus, .minus}
  complete s := by cases s <;> simp

def rootOffset : Side → ℚ
  | .plus => 0
  | .minus => 4

def pathSum (m R D : ℕ) : ℕ → List ℕ → ℚ
  | _, [] => 0
  | k, a :: w => 4 * (a : ℚ) * lambda m R D (k + 1) + pathSum m R D (k + 1) w

def left (m R D : ℕ) (s : Side) (w : List ℕ) : ℚ :=
  rootOffset s + pathSum m R D 0 w

def width (m R D : ℕ) (w : List ℕ) : ℚ :=
  if w = [] then 1 else lambda m R D w.length

def right (m R D : ℕ) (s : Side) (w : List ℕ) : ℚ :=
  left m R D s w + width m R D w

def cell (m R D : ℕ) (s : Side) (w : List ℕ) : Set ℚ :=
  Set.Icc (left m R D s w) (right m R D s w)

def BoundedAddress (D : ℕ) (w : List ℕ) : Prop := ∀ a ∈ w, a ≤ D

theorem boundedAddress_node {T : UniformTree} (v : T.Node) {D : ℕ}
    (hD : T.branchBound ≤ D) : BoundedAddress D v.val :=
  fun _ ha => (label_le_branchBound v ha).trans hD

@[simp] theorem left_nil (m R D : ℕ) (s : Side) :
    left m R D s [] = rootOffset s := by simp [left, pathSum]

@[simp] theorem width_nil (m R D : ℕ) : width m R D [] = 1 := by simp [width]

@[simp] theorem right_nil (m R D : ℕ) (s : Side) :
    right m R D s [] = rootOffset s + 1 := by simp [right]

theorem width_of_ne_nil (m R D : ℕ) {w : List ℕ} (hw : w ≠ []) :
    width m R D w = lambda m R D w.length := by simp [width, hw]

theorem width_pos (m R D : ℕ) (w : List ℕ) : 0 < width m R D w := by
  by_cases hw : w = []
  · simp [width, hw]
  · simpa [width, hw] using lambda_pos m R D w.length

theorem left_lt_right (m R D : ℕ) (s : Side) (w : List ℕ) :
    left m R D s w < right m R D s w := by
  exact lt_add_of_pos_right _ (width_pos m R D w)

theorem cell_nonempty (m R D : ℕ) (s : Side) (w : List ℕ) :
    (cell m R D s w).Nonempty :=
  ⟨left m R D s w, le_rfl, (left_lt_right m R D s w).le⟩

theorem pathSum_append (m R D k : ℕ) (u v : List ℕ) :
    pathSum m R D k (u ++ v) =
      pathSum m R D k u + pathSum m R D (k + u.length) v := by
  induction u generalizing k with
  | nil => simp [pathSum]
  | cons a u ih =>
    simp only [List.cons_append, pathSum, ih, List.length_cons]
    rw [show k + 1 + u.length = k + (u.length + 1) by omega]
    ring

theorem left_append_singleton (m R D : ℕ) (s : Side) (w : List ℕ) (a : ℕ) :
    left m R D s (w ++ [a]) =
      left m R D s w + 4 * (a : ℚ) * lambda m R D (w.length + 1) := by
  simp only [left, pathSum_append, Nat.zero_add, pathSum, add_zero]
  ring

theorem right_append_singleton (m R D : ℕ) (s : Side) (w : List ℕ) (a : ℕ) :
    right m R D s (w ++ [a]) =
      left m R D s w + (4 * (a : ℚ) + 1) * lambda m R D (w.length + 1) := by
  have hn : w ++ [a] ≠ [] := by simp
  rw [right, left_append_singleton, width_of_ne_nil m R D hn]
  simp only [List.length_append, List.length_singleton]
  ring

theorem child_endpoints (m R D : ℕ) (s : Side) (w : List ℕ) {a : ℕ}
    (ha : a ≤ D) :
    left m R D s w ≤ left m R D s (w ++ [a]) ∧
      right m R D s (w ++ [a]) ≤ right m R D s w := by
  have hscale := lambda_pos m R D (w.length + 1)
  have hcast : (a : ℚ) ≤ D := by exact_mod_cast ha
  have ha0 : (0 : ℚ) ≤ a := Nat.cast_nonneg a
  constructor
  · rw [left_append_singleton]
    nlinarith
  · rw [right_append_singleton, right]
    have hmul : (4 * (a : ℚ) + 1) * lambda m R D (w.length + 1) ≤
        (4 * (D : ℚ) + 1) * lambda m R D (w.length + 1) := by
      exact mul_le_mul_of_nonneg_right (by linarith) hscale.le
    by_cases hw : w = []
    · subst w
      have hfirst := first_children_lt_tenth m R D
      simp only [List.length_nil, Nat.zero_add, width_nil] at *
      linarith
    · rw [width_of_ne_nil m R D hw]
      have hchild := children_succ_lt_parent m R D w.length
      linarith

theorem append_endpoints (m R D : ℕ) (s : Side) (u v : List ℕ)
    (hv : BoundedAddress D v) :
    left m R D s u ≤ left m R D s (u ++ v) ∧
      right m R D s (u ++ v) ≤ right m R D s u := by
  induction v generalizing u with
  | nil => simp
  | cons a v ih =>
    have hc := child_endpoints m R D s u (hv a (by simp))
    have ht := ih (u ++ [a]) (fun b hb => hv b (by simp [hb]))
    have heq : (u ++ [a]) ++ v = u ++ a :: v := by simp [List.append_assoc]
    rw [heq] at ht
    exact ⟨hc.1.trans ht.1, ht.2.trans hc.2⟩

theorem prefix_endpoints (m R D : ℕ) (s : Side) {u v : List ℕ}
    (h : u.IsPrefix v) (hv : BoundedAddress D v) :
    left m R D s u ≤ left m R D s v ∧ right m R D s v ≤ right m R D s u := by
  obtain ⟨t, rfl⟩ := h
  exact append_endpoints m R D s u t (fun a ha => hv a (by simp [ha]))

theorem cell_subset_of_prefix (m R D : ℕ) (s : Side) {u v : List ℕ}
    (h : u.IsPrefix v) (hv : BoundedAddress D v) :
    cell m R D s v ⊆ cell m R D s u := by
  have hb := prefix_endpoints m R D s h hv
  intro x hx
  exact ⟨hb.1.trans hx.1, hx.2.trans hb.2⟩

theorem nonroot_endpoints (m R D : ℕ) (s : Side) {w : List ℕ}
    (hw : w ≠ []) (hb : BoundedAddress D w) :
    rootOffset s ≤ left m R D s w ∧ right m R D s w < rootOffset s + 1 / 10 := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons a w =>
    have ha := hb a (by simp)
    have hroot := prefix_endpoints m R D s (u := []) List.nil_prefix hb
    have hfirst := prefix_endpoints m R D s (u := [a]) ⟨w, rfl⟩ hb
    simp only [List.singleton_append] at hfirst
    have hm : (4 * (a : ℚ) + 1) * lambda m R D 1 ≤
        (4 * (D : ℚ) + 1) * lambda m R D 1 := by
      have hcast : (a : ℚ) ≤ D := by exact_mod_cast ha
      exact mul_le_mul_of_nonneg_right (by linarith) (lambda_nonneg m R D 1)
    have hf := first_children_lt_tenth m R D
    have hr := right_append_singleton m R D s [] a
    simp only [List.nil_append, List.length_nil, Nat.zero_add, left_nil] at hr
    exact ⟨by simpa only [left_nil] using hroot.1, by linarith [hfirst.2]⟩

private theorem exists_snoc_of_length_succ {w : List ℕ} {ell : ℕ}
    (h : w.length = ell + 1) :
    ∃ u a, w = u ++ [a] ∧ u.length = ell := by
  induction w using List.reverseRecOn with
  | nil => simp at h
  | append_singleton u a _ =>
    exact ⟨u, a, rfl, by simpa using h⟩

theorem same_depth_gap (m R D ell : ℕ) {s t : Side} {u v : List ℕ}
    (hu : u.length = ell) (hv : v.length = ell)
    (hbu : BoundedAddress D u) (hbv : BoundedAddress D v)
    (hne : (s, u) ≠ (t, v)) :
    right m R D s u + 3 * lambda m R D ell ≤ left m R D t v ∨
      right m R D t v + 3 * lambda m R D ell ≤ left m R D s u := by
  induction ell generalizing s t u v with
  | zero =>
    have hu0 : u = [] := List.length_eq_zero_iff.mp hu
    have hv0 : v = [] := List.length_eq_zero_iff.mp hv
    subst u
    subst v
    have hscale := lambda_le_one m R D 0
    cases s <;> cases t <;> simp only [left_nil, right_nil, rootOffset] at *
    · exact (hne rfl).elim
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
    · exact (hne rfl).elim
  | succ ell ih =>
    obtain ⟨u, a, rfl, hup⟩ := exists_snoc_of_length_succ hu
    obtain ⟨v, b, rfl, hvp⟩ := exists_snoc_of_length_succ hv
    have hau : a ≤ D := hbu a (by simp)
    have hbv' : b ≤ D := hbv b (by simp)
    have hpu : BoundedAddress D u := fun c hc => hbu c (by simp [hc])
    have hpv : BoundedAddress D v := fun c hc => hbv c (by simp [hc])
    by_cases hp : (s, u) = (t, v)
    · have hs : s = t := congrArg Prod.fst hp
      have huv : u = v := congrArg Prod.snd hp
      subst t
      subst v
      have hab : a ≠ b := by
        intro heq
        exact hne (by simp [heq])
      have hscale := lambda_nonneg m R D (ell + 1)
      rw [right_append_singleton, right_append_singleton,
        left_append_singleton, left_append_singleton, hup]
      rcases lt_or_gt_of_ne hab with hab | hba
      · left
        have hc : (a : ℚ) + 1 ≤ b := by exact_mod_cast (Nat.succ_le_iff.mpr hab)
        nlinarith
      · right
        have hc : (b : ℚ) + 1 ≤ a := by exact_mod_cast (Nat.succ_le_iff.mpr hba)
        nlinarith
    · have hgap := ih hup hvp hpu hpv hp
      have hcu := child_endpoints m R D s u hau
      have hcv := child_endpoints m R D t v hbv'
      have hscale := lambda_antitone m R D (Nat.le_succ ell)
      rcases hgap with hgap | hgap
      · left
        linarith [hcu.2, hcv.1]
      · right
        linarith [hcv.2, hcu.1]

theorem eq_of_short_intersections (m R D : ℕ) {ell L : ℕ}
    (hell : ell ≤ L) {s t : Side} {u v : List ℕ} {a b : ℚ}
    (hu : u.length = ell) (hv : v.length = ell)
    (hbu : BoundedAddress D u) (hbv : BoundedAddress D v)
    (hlen : b - a ≤ lambda m R D ell + delta m R D L)
    (hiu : (Set.Icc a b ∩ cell m R D s u).Nonempty)
    (hiv : (Set.Icc a b ∩ cell m R D t v).Nonempty) : (s, u) = (t, v) := by
  by_contra hne
  have hgap := same_depth_gap m R D ell hu hv hbu hbv hne
  obtain ⟨x, hx, hxu⟩ := hiu
  obtain ⟨y, hy, hyv⟩ := hiv
  have hshort := lambda_add_delta_lt_three m R D hell
  rcases hgap with hgap | hgap
  · linarith [hx.1, hx.2, hy.1, hy.2, hxu.1, hxu.2, hyv.1, hyv.2]
  · linarith [hx.1, hx.2, hy.1, hy.2, hxu.1, hxu.2, hyv.1, hyv.2]

def nodeCell (m R D : ℕ) (s : Side) {T : UniformTree} (v : T.Node) : Set ℚ :=
  cell m R D s v.val

theorem nodeCell_subset_of_ancestor (m R D : ℕ) (s : Side) {T : UniformTree}
    (hD : T.branchBound ≤ D) {u v : T.Node} (h : ancestor u v) :
    nodeCell m R D s v ⊆ nodeCell m R D s u :=
  cell_subset_of_prefix m R D s h (boundedAddress_node v hD)

theorem nodeCell_subset_root (m R D : ℕ) (s : Side) {T : UniformTree}
    (hD : T.branchBound ≤ D) (v : T.Node) :
    nodeCell m R D s v ⊆ Set.Icc (rootOffset s) (rootOffset s + 1) := by
  simpa [nodeCell, cell] using
    nodeCell_subset_of_ancestor m R D s hD (root_ancestor v)

theorem nonroot_nodeCell_first_tenth (m R D : ℕ) (s : Side) {T : UniformTree}
    (hD : T.branchBound ≤ D) {v : T.Node} (hv : v ≠ T.root) :
    nodeCell m R D s v ⊆ Set.Ico (rootOffset s) (rootOffset s + 1 / 10) := by
  have hn : v.val ≠ [] := by
    intro heq
    exact hv (Subtype.ext heq)
  have he := nonroot_endpoints m R D s hn (boundedAddress_node v hD)
  intro x hx
  exact ⟨he.1.trans hx.1, hx.2.trans_lt he.2⟩

theorem mem_ancestor_cell (m R D : ℕ) (s : Side) {T : UniformTree}
    (hD : T.branchBound ≤ D) (v : T.Node) (ell : ℕ) {x : ℚ}
    (hx : x ∈ nodeCell m R D s v) :
    x ∈ nodeCell m R D s (ancestorAt v ell) :=
  nodeCell_subset_of_ancestor m R D s hD (ancestorAt_ancestor v ell) hx

theorem leaf_intersection_is_ancestor (m R D : ℕ) {L ell : ℕ}
    (hell : ell ≤ L) {T U : UniformTree} (hT : T.height = L)
    (hDT : T.branchBound ≤ D) (hDU : U.branchBound ≤ D)
    {s t : Side} (v : T.Node) (hv : leaf v) (w : U.Node)
    (hw : depth w = ell) {a b x : ℚ}
    (hlen : b - a ≤ lambda m R D ell + delta m R D L)
    (hx : x ∈ Set.Icc a b) (hxv : x ∈ nodeCell m R D s v)
    (hwI : (Set.Icc a b ∩ nodeCell m R D t w).Nonempty) :
    (t, w.val) = (s, (ancestorAt v ell).val) := by
  have hdepth : depth v = L := ((leaf_iff_depth_eq_height v).mp hv).trans hT
  have hanc : depth (ancestorAt v ell) = ell :=
    depth_ancestorAt v (by simpa only [hdepth] using hell)
  exact eq_of_short_intersections m R D hell hw hanc
    (boundedAddress_node w hDU) (boundedAddress_node (ancestorAt v ell) hDT)
    hlen hwI ⟨x, hx, mem_ancestor_cell m R D s hDT v ell hxv⟩

def commonBranchBound (plus minus : UniformTree) : ℕ :=
  max plus.branchBound minus.branchBound

theorem plus_branch_le (plus minus : UniformTree) :
    plus.branchBound ≤ commonBranchBound plus minus := le_max_left _ _

theorem minus_branch_le (plus minus : UniformTree) :
    minus.branchBound ≤ commonBranchBound plus minus := le_max_right _ _

end BinPackingGap.TreeGeometry

namespace BinPackingGap.IntegerPackingArithmetic

def pathNumerator (D L : ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | k, a :: w => 40 * a * widthRadix D ^ (L - (k + 1)) +
      pathNumerator D L (k + 1) w

def rootOffsetNumerator : TreeGeometry.Side → ℕ
  | .plus => 0
  | .minus => 4

def treeLeftNumerator (m R D L : ℕ) (side : TreeGeometry.Side)
    (w : List ℕ) : ℕ :=
  rootOffsetNumerator side * geomDenominator m R D L + pathNumerator D L 0 w

def treeRightNumerator (m R D L : ℕ) (side : TreeGeometry.Side)
    (w : List ℕ) : ℕ :=
  treeLeftNumerator m R D L side w +
    if w = [] then geomDenominator m R D L else localNumerator D L w.length

theorem geomDenominator_mul_pathSum (m R D L k : ℕ) (w : List ℕ)
    (hdepth : k + w.length ≤ L) :
    (geomDenominator m R D L : ℚ) * TreeGeometry.pathSum m R D k w =
      (pathNumerator D L k w : ℚ) := by
  induction w generalizing k with
  | nil => simp [TreeGeometry.pathSum, pathNumerator]
  | cons a w ih =>
      have hdepth' : k + (w.length + 1) ≤ L := hdepth
      have hfirst : k + 1 ≤ L := by omega
      have htail : (k + 1) + w.length ≤ L := by
        omega
      have hlocal := geomDenominator_mul_lambda m R D L (k + 1) hfirst
      have hrest := ih (k + 1) htail
      simp only [TreeGeometry.pathSum, pathNumerator, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_pow]
      calc
        _ = 4 * (a : ℚ) * ((geomDenominator m R D L : ℚ) *
              Geometry.lambda m R D (k + 1)) +
            (geomDenominator m R D L : ℚ) * TreeGeometry.pathSum m R D (k + 1) w := by ring
        _ = _ := by
          rw [hlocal, hrest]
          simp only [localNumerator, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
          ring

theorem rootOffsetNumerator_cast (side : TreeGeometry.Side) :
    (rootOffsetNumerator side : ℚ) = TreeGeometry.rootOffset side := by
  cases side <;> rfl

theorem geomDenominator_mul_treeLeft (m R D L : ℕ)
    (side : TreeGeometry.Side) (w : List ℕ) (hdepth : w.length ≤ L) :
    (geomDenominator m R D L : ℚ) * TreeGeometry.left m R D side w =
      (treeLeftNumerator m R D L side w : ℚ) := by
  have hpath := geomDenominator_mul_pathSum m R D L 0 w (by simpa using hdepth)
  simp only [TreeGeometry.left, treeLeftNumerator, Nat.cast_add, Nat.cast_mul,
    rootOffsetNumerator_cast]
  rw [mul_add, hpath]
  ring

theorem geomDenominator_mul_treeRight (m R D L : ℕ)
    (side : TreeGeometry.Side) (w : List ℕ) (hdepth : w.length ≤ L) :
    (geomDenominator m R D L : ℚ) * TreeGeometry.right m R D side w =
      (treeRightNumerator m R D L side w : ℚ) := by
  have hleft := geomDenominator_mul_treeLeft m R D L side w hdepth
  simp only [TreeGeometry.right, mul_add, hleft, treeRightNumerator, Nat.cast_add]
  by_cases hw : w = []
  · simp [TreeGeometry.width, hw]
  · simp only [TreeGeometry.width, hw, ite_false]
    rw [geomDenominator_mul_lambda m R D L w.length hdepth]

end BinPackingGap.IntegerPackingArithmetic

end OAI
