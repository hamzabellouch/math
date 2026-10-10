import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import OAI.Computability.BinPacking.Trees.IntegerTreeGeometry

namespace OAI

namespace BinPackingGap

open scoped BigOperators

namespace UniformTree

instance decidableAncestor {T : UniformTree} : DecidableRel (@ancestor T) :=
  fun u v => inferInstanceAs (Decidable (u.val.IsPrefix v.val))

def prune (T : UniformTree) (keep : Finset (List ℕ))
    (hsub : keep ⊆ T.leaves) (hne : keep.Nonempty) : UniformTree where
  height := T.height
  leaves := keep
  leaves_nonempty := hne
  length_leaf := fun l hl => T.length_leaf l (hsub hl)
  positive_labels := fun l hl => T.positive_labels l (hsub hl)

@[simp] theorem prune_height (T : UniformTree) (keep : Finset (List ℕ))
    (hsub : keep ⊆ T.leaves) (hne : keep.Nonempty) :
    (T.prune keep hsub hne).height = T.height := rfl

@[simp] theorem prune_leaves (T : UniformTree) (keep : Finset (List ℕ))
    (hsub : keep ⊆ T.leaves) (hne : keep.Nonempty) :
    (T.prune keep hsub hne).leaves = keep := rfl

theorem prune_vertices_subset (T : UniformTree) (keep : Finset (List ℕ))
    (hsub : keep ⊆ T.leaves) (hne : keep.Nonempty) :
    (T.prune keep hsub hne).vertices ⊆ T.vertices := by
  intro w hw
  obtain ⟨l, hl, hwl⟩ := (T.prune keep hsub hne).mem_vertices_iff.mp hw
  exact T.mem_vertices_iff.mpr ⟨l, hsub hl, hwl⟩

def pruneEmbedding (T : UniformTree) (keep : Finset (List ℕ))
    (hsub : keep ⊆ T.leaves) (hne : keep.Nonempty) :
    (T.prune keep hsub hne).Node ↪ T.Node where
  toFun v := ⟨v.val, T.prune_vertices_subset keep hsub hne v.property⟩
  inj' := fun _ _ h => Subtype.ext (congrArg (fun v : T.Node => v.val) h)

@[simp] theorem pruneEmbedding_val (T : UniformTree) (keep : Finset (List ℕ))
    (hsub : keep ⊆ T.leaves) (hne : keep.Nonempty)
    (v : (T.prune keep hsub hne).Node) :
    (T.pruneEmbedding keep hsub hne v).val = v.val := rfl

@[simp] theorem pruneEmbedding_depth (T : UniformTree) (keep : Finset (List ℕ))
    (hsub : keep ⊆ T.leaves) (hne : keep.Nonempty)
    (v : (T.prune keep hsub hne).Node) :
    depth (T.pruneEmbedding keep hsub hne v) = depth v := rfl

@[simp] theorem pruneEmbedding_ancestor (T : UniformTree) (keep : Finset (List ℕ))
    (hsub : keep ⊆ T.leaves) (hne : keep.Nonempty)
    (u v : (T.prune keep hsub hne).Node) :
    ancestor (T.pruneEmbedding keep hsub hne u)
      (T.pruneEmbedding keep hsub hne v) ↔ ancestor u v := Iff.rfl

@[simp] theorem pruneEmbedding_child (T : UniformTree) (keep : Finset (List ℕ))
    (hsub : keep ⊆ T.leaves) (hne : keep.Nonempty)
    (u v : (T.prune keep hsub hne).Node) :
    child (T.pruneEmbedding keep hsub hne u)
      (T.pruneEmbedding keep hsub hne v) ↔ child u v := Iff.rfl

def projectMarks {T : UniformTree} (A : Finset T.Node) : Finset (List ℕ) :=
  A.image Subtype.val

@[simp] theorem mem_projectMarks {T : UniformTree} (A : Finset T.Node)
    (w : List ℕ) : w ∈ projectMarks A ↔ ∃ v ∈ A, v.val = w := by
  simp only [projectMarks, Finset.mem_image]

theorem projectMarks_filter_card {T : UniformTree} (A : Finset T.Node)
    (p : List ℕ → Prop) [DecidablePred p] :
    ((projectMarks A).filter p).card =
      (A.filter (fun v => p v.val)).card := by
  classical
  have heq : (projectMarks A).filter p =
      (A.filter (fun v => p v.val)).image Subtype.val := by
    ext w
    constructor
    · intro hw
      obtain ⟨hwA, hp⟩ := Finset.mem_filter.mp hw
      obtain ⟨v, hv, rfl⟩ := (mem_projectMarks A w).mp hwA
      exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hp⟩, rfl⟩
    · intro hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_filter.mpr
        ⟨(mem_projectMarks A v.val).mpr ⟨v, (Finset.mem_filter.mp hv).1, rfl⟩,
          (Finset.mem_filter.mp hv).2⟩
  rw [heq, Finset.card_image_of_injective _ Subtype.val_injective]

theorem levelCount_projectMarks {T : UniformTree} (A : Finset T.Node) (ℓ : ℕ) :
    levelCount (projectMarks A) ℓ = (A.filter (fun v => depth v = ℓ)).card :=
  projectMarks_filter_card A (fun w => w.length = ℓ)

theorem colorCount_projectMarks {T : UniformTree} (A : Finset T.Node) (l : T.Node) :
    colorCount (projectMarks A) l.val = (A.filter (fun v => ancestor v l)).card :=
  projectMarks_filter_card A (fun w => w.IsPrefix l.val)

theorem root_not_projectMarks {T : UniformTree} (A : Finset T.Node)
    (h : T.root ∉ A) : [] ∉ projectMarks A := by
  intro hm
  obtain ⟨v, hv, hval⟩ := (mem_projectMarks A []).mp hm
  have heq : v = T.root := Subtype.ext hval
  exact h (heq ▸ hv)

def retainMarks (T : UniformTree) (marks : Finset (List ℕ)) : Finset T.Node :=
  Finset.univ.filter (fun v => v.val ∈ marks)

@[simp] theorem mem_retainMarks (T : UniformTree) (marks : Finset (List ℕ))
    (v : T.Node) : v ∈ T.retainMarks marks ↔ v.val ∈ marks := by
  simp only [retainMarks, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_project_retainMarks (T : UniformTree) (marks : Finset (List ℕ))
    (w : List ℕ) : w ∈ projectMarks (T.retainMarks marks) ↔
      w ∈ marks ∧ w ∈ T.vertices := by
  constructor
  · intro hw
    obtain ⟨v, hv, rfl⟩ := (mem_projectMarks _ w).mp hw
    exact ⟨(mem_retainMarks T marks v).mp hv, v.property⟩
  · rintro ⟨hw, hv⟩
    exact (mem_projectMarks _ w).mpr
      ⟨⟨w, hv⟩, (mem_retainMarks T marks ⟨w, hv⟩).mpr hw, rfl⟩

theorem retainMarks_root_not_mem (T : UniformTree) (marks : Finset (List ℕ))
    (h : [] ∉ marks) : T.root ∉ T.retainMarks marks := by
  simpa only [mem_retainMarks, root_val] using h

theorem retainMarks_level_le (T : UniformTree) (marks : Finset (List ℕ)) (ℓ : ℕ) :
    ((T.retainMarks marks).filter (fun v => depth v = ℓ)).card ≤
      levelCount marks ℓ := by
  rw [← levelCount_projectMarks]
  apply Finset.card_le_card
  intro w hw
  obtain ⟨hw, hlen⟩ := Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨((T.mem_project_retainMarks marks w).mp hw).1, hlen⟩

theorem retainMarks_leaf_count (T : UniformTree) (marks : Finset (List ℕ))
    (l : T.Node) (hl : leaf l) :
    ((T.retainMarks marks).filter (fun v => ancestor v l)).card =
      colorCount marks l.val := by
  rw [← colorCount_projectMarks]
  apply congrArg Finset.card
  ext w
  constructor
  · intro hw
    obtain ⟨hw, hp⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨((T.mem_project_retainMarks marks w).mp hw).1, hp⟩
  · intro hw
    obtain ⟨hw, hp⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr
      ⟨(T.mem_project_retainMarks marks w).mpr
        ⟨hw, T.mem_vertices_iff.mpr ⟨l.val, hl, hp⟩⟩, hp⟩

end UniformTree

open UniformTree

structure CompetingTrees (d : ℕ) where
  plus : UniformTree
  minus : UniformTree
  height : ℕ
  height_pos : 0 < height
  plus_height : plus.height = height
  minus_height : minus.height = height
  quota : ℕ → ℕ
  quota_pos : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ height → 0 < quota ℓ
  markingPlus : Finset plus.Node
  markingMinus : Finset minus.Node
  plus_root_not_marked : plus.root ∉ markingPlus
  minus_root_not_marked : minus.root ∉ markingMinus
  plus_quota : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ height →
    (markingPlus.filter (fun v => depth v = ℓ)).card ≤ quota ℓ
  minus_quota : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ height →
    (markingMinus.filter (fun v => depth v = ℓ)).card ≤ quota ℓ
  plus_rich : ∀ l : plus.Node, leaf l →
    d ≤ (markingPlus.filter (fun v => ancestor v l)).card
  minus_rich : ∀ l : minus.Node, leaf l →
    d ≤ (markingMinus.filter (fun v => ancestor v l)).card
  shared_obstruction : ∀ (Aplus : Finset plus.Node) (Aminus : Finset minus.Node),
    plus.root ∉ Aplus → minus.root ∉ Aminus →
    (∀ ℓ, 1 ≤ ℓ → ℓ ≤ height →
      (Aplus.filter (fun v => depth v = ℓ)).card +
      (Aminus.filter (fun v => depth v = ℓ)).card ≤ quota ℓ) →
    (∃ l : plus.Node, leaf l ∧ ∀ v ∈ Aplus, ¬ ancestor v l) ∨
    (∃ l : minus.Node, leaf l ∧ ∀ v ∈ Aminus, ¬ ancestor v l)

namespace AuxiliaryTree

def richLeaves {n : ℕ} (aux : AuxiliaryTree n)
    (marks : Finset (List ℕ)) (d : ℕ) : Finset (List ℕ) :=
  aux.tree.leaves.filter (fun l => d ≤ colorCount marks l)

theorem richLeaves_subset {n : ℕ} (aux : AuxiliaryTree n)
    (marks : Finset (List ℕ)) (d : ℕ) :
    aux.richLeaves marks d ⊆ aux.tree.leaves := Finset.filter_subset _ _

theorem richLeaves_nonempty {n d : ℕ} (aux : AuxiliaryTree n)
    (marks : Finset (List ℕ)) (h : d ≤ n)
    (hw : ∃ l ∈ aux.tree.leaves, colorCount marks l = n) :
    (aux.richLeaves marks d).Nonempty := by
  obtain ⟨l, hl, heq⟩ := hw
  exact ⟨l, Finset.mem_filter.mpr ⟨hl, heq.symm ▸ h⟩⟩

theorem richLeaves_cover {d : ℕ} (aux : AuxiliaryTree (2 * d - 1))
    (l : List ℕ) (hl : l ∈ aux.tree.leaves) :
    l ∈ aux.richLeaves aux.red d ∨ l ∈ aux.richLeaves aux.blue d := by
  have htotal := aux.total_count l hl
  have hrich : d ≤ colorCount aux.red l ∨ d ≤ colorCount aux.blue l := by omega
  exact hrich.imp (fun h => Finset.mem_filter.mpr ⟨hl, h⟩)
    (fun h => Finset.mem_filter.mpr ⟨hl, h⟩)

theorem height_pos {n : ℕ} (aux : AuxiliaryTree n) (hn : 0 < n) :
    0 < aux.tree.height := by
  obtain ⟨l, hl, hcount⟩ := aux.red_witness
  by_contra hpos
  have hheight : aux.tree.height = 0 := by omega
  have hl_nil : l = [] := List.length_eq_zero_iff.mp ((aux.tree.length_leaf l hl).trans hheight)
  have hempty : aux.red.filter (fun w => w.IsPrefix l) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨hred, hp⟩ := Finset.mem_filter.mp hw
    have hw_nil : w = [] := by
      apply List.length_eq_zero_iff.mp
      have hle := hp.length_le
      rw [hl_nil] at hle
      exact Nat.eq_zero_of_le_zero hle
    exact aux.root_not_red (hw_nil ▸ hred)
  have hz : colorCount aux.red l = 0 := by rw [colorCount, hempty, Finset.card_empty]
  omega

def richTree {n d : ℕ} (aux : AuxiliaryTree n) (marks : Finset (List ℕ))
    (hne : (aux.richLeaves marks d).Nonempty) : UniformTree :=
  aux.tree.prune (aux.richLeaves marks d) (aux.richLeaves_subset marks d) hne

end AuxiliaryTree

theorem levelCount_project_union {T U : UniformTree}
    (A : Finset T.Node) (B : Finset U.Node) (ℓ : ℕ) :
    levelCount (projectMarks A ∪ projectMarks B) ℓ ≤
      (A.filter (fun v => depth v = ℓ)).card +
      (B.filter (fun v => depth v = ℓ)).card := by
  have heq : (projectMarks A ∪ projectMarks B).filter (fun w => w.length = ℓ) =
      (projectMarks A).filter (fun w => w.length = ℓ) ∪
      (projectMarks B).filter (fun w => w.length = ℓ) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_union, or_and_right]
  unfold levelCount
  rw [heq]
  exact (Finset.card_union_le _ _).trans_eq
    (congrArg₂ (· + ·) (levelCount_projectMarks A ℓ) (levelCount_projectMarks B ℓ))

namespace CompetingTrees

def quotaTotal {d : ℕ} (T : CompetingTrees d) : ℕ :=
  ∑ ℓ ∈ Finset.Icc 1 T.height, T.quota ℓ

theorem markingPlus_depth_pos {d : ℕ} (T : CompetingTrees d)
    (v : T.plus.Node) (hv : v ∈ T.markingPlus) : 0 < depth v := by
  have hne : v ≠ T.plus.root := fun h => T.plus_root_not_marked (h ▸ hv)
  have hn := mt (eq_root_iff_depth_eq_zero v).mpr hne
  exact Nat.pos_of_ne_zero hn

theorem markingMinus_depth_pos {d : ℕ} (T : CompetingTrees d)
    (v : T.minus.Node) (hv : v ∈ T.markingMinus) : 0 < depth v := by
  have hne : v ≠ T.minus.root := fun h => T.minus_root_not_marked (h ▸ hv)
  have hn := mt (eq_root_iff_depth_eq_zero v).mpr hne
  exact Nat.pos_of_ne_zero hn

def ofAuxiliary (d : ℕ) (hd : 0 < d) (aux : AuxiliaryTree (2 * d - 1)) :
    CompetingTrees d := by
  have hdn : d ≤ 2 * d - 1 := by omega
  have hred := aux.richLeaves_nonempty aux.red hdn aux.red_witness
  have hblue := aux.richLeaves_nonempty aux.blue hdn aux.blue_witness
  let plus := aux.richTree aux.red hred
  let minus := aux.richTree aux.blue hblue
  refine
    { plus := plus
      minus := minus
      height := aux.tree.height
      height_pos := aux.height_pos (by omega)
      plus_height := rfl
      minus_height := rfl
      quota := aux.quota
      quota_pos := aux.quota_pos
      markingPlus := plus.retainMarks aux.red
      markingMinus := minus.retainMarks aux.blue
      plus_root_not_marked := plus.retainMarks_root_not_mem aux.red aux.root_not_red
      minus_root_not_marked := minus.retainMarks_root_not_mem aux.blue aux.root_not_blue
      plus_quota := ?_
      minus_quota := ?_
      plus_rich := ?_
      minus_rich := ?_
      shared_obstruction := ?_ }
  · intro ℓ hℓ hℓ'
    exact (plus.retainMarks_level_le aux.red ℓ).trans (aux.red_level ℓ hℓ hℓ')
  · intro ℓ hℓ hℓ'
    exact (minus.retainMarks_level_le aux.blue ℓ).trans (aux.blue_level ℓ hℓ hℓ')
  · intro l hl
    rw [plus.retainMarks_leaf_count aux.red l hl]
    exact (Finset.mem_filter.mp hl).2
  · intro l hl
    rw [minus.retainMarks_leaf_count aux.blue l hl]
    exact (Finset.mem_filter.mp hl).2
  · intro A B hA hB hquota
    have hproject : RespectsTreeQuota aux.tree aux.quota (projectMarks A ∪ projectMarks B) := by
      constructor
      · intro h
        rcases Finset.mem_union.mp h with h | h
        · exact root_not_projectMarks A hA h
        · exact root_not_projectMarks B hB h
      · intro ℓ hℓ hℓ'
        exact (levelCount_project_union A B ℓ).trans (hquota ℓ hℓ hℓ')
    obtain ⟨l, hl, havoid⟩ := aux.avoids _ hproject
    rcases aux.richLeaves_cover l hl with hredLeaf | hblueLeaf
    · left
      have hlplus : l ∈ plus.leaves := hredLeaf
      refine ⟨⟨l, plus.leaf_mem_vertices hlplus⟩, hlplus, ?_⟩
      intro v hv hp
      exact Finset.disjoint_left.mp havoid
        (Finset.mem_union_left _ ((mem_projectMarks A v.val).mpr ⟨v, hv, rfl⟩))
        (mem_prefixes_iff.mpr hp)
    · right
      have hlminus : l ∈ minus.leaves := hblueLeaf
      refine ⟨⟨l, minus.leaf_mem_vertices hlminus⟩, hlminus, ?_⟩
      intro v hv hp
      exact Finset.disjoint_left.mp havoid
        (Finset.mem_union_right _ ((mem_projectMarks B v.val).mpr ⟨v, hv, rfl⟩))
        (mem_prefixes_iff.mpr hp)

end CompetingTrees

end BinPackingGap

end OAI
