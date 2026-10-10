import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex
import OAI.Computability.BinPacking.Trees.TreeAvoidance

namespace OAI

namespace BinPackingGap

namespace UniformTree

def leafRank (T : UniformTree) (l : T.leaves) : ℕ :=
  ((T.leaves.orderIsoOfFin rfl).symm l).val + 1

theorem leafRank_pos (T : UniformTree) (l : T.leaves) : 0 < T.leafRank l := by
  unfold leafRank
  omega

theorem one_le_leafRank (T : UniformTree) (l : T.leaves) : 1 ≤ T.leafRank l :=
  T.leafRank_pos l

theorem leafRank_le (T : UniformTree) (l : T.leaves) : T.leafRank l ≤ T.leaves.card := by
  have h := ((T.leaves.orderIsoOfFin rfl).symm l).isLt
  unfold leafRank
  omega

theorem leafRank_injective (T : UniformTree) : Function.Injective T.leafRank := by
  intro l m h
  apply (T.leaves.orderIsoOfFin rfl).symm.injective
  apply Fin.ext
  exact Nat.add_right_cancel h

theorem leaf_card_pos (T : UniformTree) : 0 < T.leaves.card :=
  Finset.card_pos.mpr T.leaves_nonempty

def rankedGadget (T : UniformTree) (l : T.leaves) : AuxiliaryTree 1 :=
  ForkGadget.auxiliary T.leaves.card (T.leafRank l)
    (T.one_le_leafRank l) (T.leafRank_le l)

@[simp] theorem rankedGadget_height (T : UniformTree) (l : T.leaves) :
    (T.rankedGadget l).tree.height = T.leaves.card := rfl

@[simp] theorem rankedGadget_quota (T : UniformTree) (l : T.leaves) :
    (T.rankedGadget l).quota = phaseQuota := rfl

theorem rankedGadget_red_depth (T : UniformTree) (l : T.leaves)
    {w : List ℕ} (hw : w ∈ (T.rankedGadget l).red) : w.length = T.leafRank l :=
  ForkGadget.auxiliary_red_depth _ _ _ _ hw

theorem rankedGadget_blue_depth (T : UniformTree) (l : T.leaves)
    {w : List ℕ} (hw : w ∈ (T.rankedGadget l).blue) : w.length = T.leafRank l :=
  ForkGadget.auxiliary_blue_depth _ _ _ _ hw

@[simp] theorem rankedGadget_card_red (T : UniformTree) (l : T.leaves) :
    (T.rankedGadget l).red.card = phaseQuota (T.leafRank l) :=
  ForkGadget.auxiliary_card_red _ _ _ _

@[simp] theorem rankedGadget_card_blue (T : UniformTree) (l : T.leaves) :
    (T.rankedGadget l).blue.card = phaseQuota (T.leafRank l) :=
  ForkGadget.auxiliary_card_blue _ _ _ _

def nextPhase (T : UniformTree) : UniformTree :=
  T.graft (fun l => (T.rankedGadget l).tree) T.leaves.card
    (fun l => T.rankedGadget_height l)

@[simp] theorem nextPhase_height (T : UniformTree) :
    T.nextPhase.height = T.height + T.leaves.card := rfl

theorem height_lt_nextPhase (T : UniformTree) : T.height < T.nextPhase.height := by
  rw [nextPhase_height]
  exact Nat.lt_add_of_pos_right T.leaf_card_pos

theorem mem_nextPhase_leaves (T : UniformTree) {x : List ℕ} :
    x ∈ T.nextPhase.leaves ↔
      ∃ l : T.leaves, ∃ w ∈ (T.rankedGadget l).tree.leaves, x = l.val ++ w :=
  T.mem_graft_leaves _ _ _

def singletonRoot : UniformTree where
  height := 0
  leaves := {[]}
  leaves_nonempty := ⟨[], Finset.mem_singleton_self []⟩
  length_leaf := by
    intro l hl
    have hl' : l = [] := Finset.mem_singleton.mp hl
    simp only [hl', List.length_nil]
  positive_labels := by
    intro l hl a ha
    have hl' : l = [] := Finset.mem_singleton.mp hl
    simp only [hl', List.not_mem_nil] at ha

end UniformTree

namespace AuxiliaryTree

def initial : AuxiliaryTree 0 where
  tree := UniformTree.singletonRoot
  quota := fun _ => 0
  quota_pos := by
    intro depth hpos hle
    change depth ≤ 0 at hle
    omega
  red := ∅
  blue := ∅
  red_subset := Finset.empty_subset _
  blue_subset := Finset.empty_subset _
  root_not_red := by simp
  root_not_blue := by simp
  red_blue_disjoint := by simp
  red_level := by simp [levelCount]
  blue_level := by simp [levelCount]
  total_count := by simp [colorCount]
  red_witness := ⟨[], Finset.mem_singleton_self [], by simp [colorCount]⟩
  blue_witness := ⟨[], Finset.mem_singleton_self [], by simp [colorCount]⟩
  avoids := by
    intro marks hmarks
    refine ⟨[], Finset.mem_singleton_self [], ?_⟩
    apply Finset.disjoint_left.mpr
    intro w hw hp
    have heq : w = [] := by
      simpa only [UniformTree.mem_prefixes_iff, List.prefix_nil] using hp
    exact hmarks.1 (heq ▸ hw)

def step {n : ℕ} (old : AuxiliaryTree n) : AuxiliaryTree (n + 1) where
  tree := old.tree.nextPhase
  quota := extendPhaseQuota old.tree.height old.quota
  quota_pos := by
    intro depth hpos _
    unfold extendPhaseQuota
    split_ifs with hdepth
    · exact old.quota_pos depth hpos hdepth
    · exact phaseQuota_pos _
  red := old.red ∪ old.tree.liftMarks (fun l => (old.tree.rankedGadget l).red)
  blue := old.blue ∪ old.tree.liftMarks (fun l => (old.tree.rankedGadget l).blue)
  red_subset := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact old.tree.vertices_subset_graft _ _ _ (old.red_subset hw)
    · exact old.tree.liftMarks_subset_graft_vertices _ _ _ _
        (fun l => (old.tree.rankedGadget l).red_subset) hw
  blue_subset := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact old.tree.vertices_subset_graft _ _ _ (old.blue_subset hw)
    · exact old.tree.liftMarks_subset_graft_vertices _ _ _ _
        (fun l => (old.tree.rankedGadget l).blue_subset) hw
  root_not_red := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact old.root_not_red h
    · exact old.tree.root_not_mem_lift _
        (fun l => (old.tree.rankedGadget l).root_not_red) h
  root_not_blue := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact old.root_not_blue h
    · exact old.tree.root_not_mem_lift _
        (fun l => (old.tree.rankedGadget l).root_not_blue) h
  red_blue_disjoint := by
    apply Finset.disjoint_left.mpr
    intro w hr hb
    rcases Finset.mem_union.mp hr with hr | hr <;>
      rcases Finset.mem_union.mp hb with hb | hb
    · exact Finset.disjoint_left.mp old.red_blue_disjoint hr hb
    · exact Finset.disjoint_left.mp
        (old.tree.old_marks_disjoint_lift old.red _ old.red_subset
          (fun l => (old.tree.rankedGadget l).root_not_blue)) hr hb
    · exact Finset.disjoint_left.mp
        (old.tree.old_marks_disjoint_lift old.blue _ old.blue_subset
          (fun l => (old.tree.rankedGadget l).root_not_red)) hb hr
    · exact Finset.disjoint_left.mp
        (old.tree.liftMarks_disjoint _ _
          (fun l => (old.tree.rankedGadget l).red_blue_disjoint)) hr hb
  red_level := by
    intro depth hpos _
    simpa only [extendPhaseQuota] using
      old.tree.levelCount_union_liftMarks_le old.red
        (fun l => (old.tree.rankedGadget l).red)
        old.red_subset (fun l => (old.tree.rankedGadget l).root_not_red)
        old.tree.leafRank old.tree.leafRank_injective
        (fun l _ hw => old.tree.rankedGadget_red_depth l hw)
        (fun l => (old.tree.rankedGadget_card_red l).le)
        old.quota old.red_level depth hpos
  blue_level := by
    intro depth hpos _
    simpa only [extendPhaseQuota] using
      old.tree.levelCount_union_liftMarks_le old.blue
        (fun l => (old.tree.rankedGadget l).blue)
        old.blue_subset (fun l => (old.tree.rankedGadget l).root_not_blue)
        old.tree.leafRank old.tree.leafRank_injective
        (fun l _ hw => old.tree.rankedGadget_blue_depth l hw)
        (fun l => (old.tree.rankedGadget_card_blue l).le)
        old.quota old.blue_level depth hpos
  total_count := by
    intro leaf hleaf
    obtain ⟨l, w, hw, rfl⟩ := old.tree.mem_nextPhase_leaves.mp hleaf
    rw [old.tree.colorCount_union_liftMarks old.red _ old.red_subset
        (fun l => (old.tree.rankedGadget l).root_not_red),
      old.tree.colorCount_union_liftMarks old.blue _ old.blue_subset
        (fun l => (old.tree.rankedGadget l).root_not_blue)]
    have hold := old.total_count l.val l.property
    have hnew := (old.tree.rankedGadget l).total_count w hw
    omega
  red_witness := by
    obtain ⟨l, hl, hold⟩ := old.red_witness
    let leaf : old.tree.leaves := ⟨l, hl⟩
    obtain ⟨w, hw, hnew⟩ := (old.tree.rankedGadget leaf).red_witness
    refine ⟨l ++ w, old.tree.mem_nextPhase_leaves.mpr ⟨leaf, w, hw, rfl⟩, ?_⟩
    change colorCount (old.red ∪ old.tree.liftMarks
      (fun l => (old.tree.rankedGadget l).red)) (leaf.val ++ w) = n + 1
    rw [old.tree.colorCount_union_liftMarks old.red _ old.red_subset
      (fun l => (old.tree.rankedGadget l).root_not_red) leaf w]
    exact congrArg₂ (· + ·) hold hnew
  blue_witness := by
    obtain ⟨l, hl, hold⟩ := old.blue_witness
    let leaf : old.tree.leaves := ⟨l, hl⟩
    obtain ⟨w, hw, hnew⟩ := (old.tree.rankedGadget leaf).blue_witness
    refine ⟨l ++ w, old.tree.mem_nextPhase_leaves.mpr ⟨leaf, w, hw, rfl⟩, ?_⟩
    change colorCount (old.blue ∪ old.tree.liftMarks
      (fun l => (old.tree.rankedGadget l).blue)) (leaf.val ++ w) = n + 1
    rw [old.tree.colorCount_union_liftMarks old.blue _ old.blue_subset
      (fun l => (old.tree.rankedGadget l).root_not_blue) leaf w]
    exact congrArg₂ (· + ·) hold hnew
  avoids := graft_avoids old old.tree.rankedGadget old.tree.leaves.card
    old.tree.rankedGadget_height old.tree.rankedGadget_quota

@[simp] theorem step_height {n : ℕ} (old : AuxiliaryTree n) :
    old.step.tree.height = old.tree.height + old.tree.leaves.card := rfl

theorem height_lt_step {n : ℕ} (old : AuxiliaryTree n) :
    old.tree.height < old.step.tree.height := old.tree.height_lt_nextPhase

end AuxiliaryTree

def buildAuxiliary : (n : ℕ) → AuxiliaryTree n
  | 0 => AuxiliaryTree.initial
  | n + 1 => (buildAuxiliary n).step

@[simp] theorem buildAuxiliary_zero : buildAuxiliary 0 = AuxiliaryTree.initial := rfl

@[simp] theorem buildAuxiliary_succ (n : ℕ) :
    buildAuxiliary (n + 1) = (buildAuxiliary n).step := rfl

theorem phases_le_buildAuxiliary_height (n : ℕ) : n ≤ (buildAuxiliary n).tree.height := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      have h := (buildAuxiliary n).height_lt_step
      change n + 1 ≤ (buildAuxiliary n).step.tree.height
      omega

theorem buildAuxiliary_height_pos {n : ℕ} (hn : 0 < n) :
    0 < (buildAuxiliary n).tree.height :=
  lt_of_lt_of_le hn (phases_le_buildAuxiliary_height n)

end BinPackingGap

end OAI
