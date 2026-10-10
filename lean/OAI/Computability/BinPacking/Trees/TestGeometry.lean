import Mathlib.Order.Interval.Set.Disjoint
import OAI.Computability.BinPacking.Inventory.InventoryScores
import OAI.Computability.BinPacking.Packing.CoordinateOrder

namespace OAI

namespace BinPackingGap.Geometry

variable {m R D L : ℕ}

def jobLeft (m R D L : ℕ) (r : Position m R) : ℚ :=
  baseline m R r - delta m R D L

def closedJobCell (m R D L : ℕ) (r : Position m R) : Set ℚ :=
  Set.Icc (jobLeft m R D L r) (baseline m R r)

def jobTestInterval (m R D L : ℕ) (r : Position m R) : Set ℚ :=
  Set.Ico (jobLeft m R D L r) (baseline m R r)

def jobInterior (m R D L : ℕ) (r : Position m R) : ℚ :=
  baseline m R r - delta m R D L / 2

theorem closed_interval_gap_le_length {a b l₁ u₁ l₂ u₂ : ℚ}
    (h₁ : (Set.Icc a b ∩ Set.Icc l₁ u₁).Nonempty)
    (h₂ : (Set.Icc a b ∩ Set.Icc l₂ u₂).Nonempty) :
    l₂ - u₁ ≤ b - a := by
  rcases h₁ with ⟨x, hx⟩
  rcases h₂ with ⟨y, hy⟩
  have hax := hx.1.1
  have hxu := hx.2.2
  have hly := hy.2.1
  have hyb := hy.1.2
  linarith

theorem closed_interval_cannot_meet_of_lt_gap {a b l₁ u₁ l₂ u₂ : ℚ}
    (hlen : b - a < l₂ - u₁)
    (h₁ : (Set.Icc a b ∩ Set.Icc l₁ u₁).Nonempty)
    (h₂ : (Set.Icc a b ∩ Set.Icc l₂ u₂).Nonempty) : False :=
  (not_le_of_gt hlen) (closed_interval_gap_le_length h₁ h₂)

theorem jobLeft_lt_baseline (m R D L : ℕ) (r : Position m R) :
    jobLeft m R D L r < baseline m R r := by
  have h := delta_pos m R D L
  unfold jobLeft
  linarith

theorem one_tenth_lt_jobLeft (m R D L : ℕ) (r : Position m R) :
    1 / 10 < jobLeft m R D L r := by
  have hb := baseline_lower m R r
  have hd := delta_lt_gap m R D L
  have hg := gap_le_one_sixteen m R
  unfold jobLeft
  linarith

theorem job_baseline_lt_one (m R : ℕ) (r : Position m R) :
    baseline m R r < 1 := by
  have h := baseline_upper m R r
  linarith

theorem closedJobCell_bounds {r : Position m R} {x : ℚ}
    (hx : x ∈ closedJobCell m R D L r) : 1 / 10 < x ∧ x < 1 := by
  exact ⟨lt_of_lt_of_le (one_tenth_lt_jobLeft m R D L r) hx.1,
    lt_of_le_of_lt hx.2 (job_baseline_lt_one m R r)⟩

theorem closedJobCell_subset_plusRoot (m R D L : ℕ) (r : Position m R) :
    closedJobCell m R D L r ⊆ Set.Icc 0 1 := by
  intro x hx
  obtain ⟨hleft, hright⟩ := closedJobCell_bounds hx
  exact ⟨by linarith, hright.le⟩

theorem jobTestInterval_subset_closedJobCell (m R D L : ℕ) (r : Position m R) :
    jobTestInterval m R D L r ⊆ closedJobCell m R D L r := by
  intro x hx
  exact ⟨hx.1, hx.2.le⟩

theorem job_gap_of_posLT (D L : ℕ) {r s : Position m R} (hrs : posLT r s) :
    gap m R - delta m R D L ≤ jobLeft m R D L s - baseline m R r := by
  have h := baseline_gap_of_posLT hrs
  unfold jobLeft
  linarith

theorem baseline_lt_jobLeft_of_posLT (D L : ℕ) {r s : Position m R}
    (hrs : posLT r s) : baseline m R r < jobLeft m R D L s := by
  have hgap := job_gap_of_posLT D L hrs
  have hd := delta_lt_gap m R D L
  linarith

theorem closedJobCell_disjoint {r s : Position m R} (hrs : r ≠ s) :
    Disjoint (closedJobCell m R D L r) (closedJobCell m R D L s) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases posLT_or_posLT_of_ne hrs with hlt | hlt
  · have h := baseline_lt_jobLeft_of_posLT D L hlt
    exact (not_le_of_gt h) (hy.1.trans hx.2)
  · have h := baseline_lt_jobLeft_of_posLT D L hlt
    exact (not_le_of_gt h) (hx.1.trans hy.2)

theorem jobTestInterval_disjoint {r s : Position m R} (hrs : r ≠ s) :
    Disjoint (jobTestInterval m R D L r) (jobTestInterval m R D L s) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact Set.disjoint_left.mp (closedJobCell_disjoint hrs)
    (jobTestInterval_subset_closedJobCell m R D L r hx)
    (jobTestInterval_subset_closedJobCell m R D L s hy)

theorem closedJobCell_unique_of_short_interval (hL : 1 ≤ L)
    {a b : ℚ} {r s : Position m R}
    (hlen : b - a ≤ lambda m R D 1 + delta m R D L)
    (hr : (Set.Icc a b ∩ closedJobCell m R D L r).Nonempty)
    (hs : (Set.Icc a b ∩ closedJobCell m R D L s).Nonempty) : r = s := by
  have hwidth := lambda_one_add_two_delta_lt_gap m R D hL
  rcases posLT_trichotomy r s with hrs | hrs | hsr
  · have hgap := job_gap_of_posLT D L hrs
    have hspan := closed_interval_gap_le_length hr hs
    linarith
  · exact hrs
  · have hgap := job_gap_of_posLT D L hsr
    have hspan := closed_interval_gap_le_length hs hr
    linarith

theorem closedJobCell_unique_of_short_halfOpen (hL : 1 ≤ L)
    {a b : ℚ} {r s : Position m R}
    (hlen : b - a ≤ lambda m R D 1 + delta m R D L)
    (hr : (Set.Ico a b ∩ closedJobCell m R D L r).Nonempty)
    (hs : (Set.Ico a b ∩ closedJobCell m R D L s).Nonempty) : r = s := by
  apply closedJobCell_unique_of_short_interval hL hlen
  · rcases hr with ⟨x, hx⟩
    exact ⟨x, ⟨hx.1.1, hx.1.2.le⟩, hx.2⟩
  · rcases hs with ⟨x, hx⟩
    exact ⟨x, ⟨hx.1.1, hx.1.2.le⟩, hx.2⟩

theorem jobInterior_mem_jobTestInterval (m R D L : ℕ) (r : Position m R) :
    jobInterior m R D L r ∈ jobTestInterval m R D L r :=
  jobInterior_mem_current (delta_pos m R D L) r

theorem jobInterior_mem_closedJobCell (m R D L : ℕ) (r : Position m R) :
    jobInterior m R D L r ∈ closedJobCell m R D L r :=
  jobTestInterval_subset_closedJobCell m R D L r
    (jobInterior_mem_jobTestInterval m R D L r)

theorem baseline_le_jobInterior (D L : ℕ) {r s : Position m R} :
    baseline m R s ≤ jobInterior m R D L r ↔ posLT s r :=
  baseline_le_actualJobInterior_iff D L

theorem jobInterior_mem_jobTestInterval_iff (D L : ℕ) {r s : Position m R} :
    jobInterior m R D L r ∈ jobTestInterval m R D L s ↔ s = r :=
  actualJobInterior_mem_job_iff D L

end BinPackingGap.Geometry

namespace BinPackingGap.InventoryData

variable (D : InventoryData)

def geometryBound : ℕ := TreeGeometry.commonBranchBound D.plus D.minus

theorem plus_branch_le_geometryBound : D.plus.branchBound ≤ D.geometryBound :=
  TreeGeometry.plus_branch_le D.plus D.minus

theorem minus_branch_le_geometryBound : D.minus.branchBound ≤ D.geometryBound :=
  TreeGeometry.minus_branch_le D.plus D.minus

def incidencePosition {v : D.Vertex} (j : D.IncidencePosition v) : D.Position :=
  (j.1.val.1, j.2)

theorem incidencePosition_injective (v : D.Vertex) :
    Function.Injective (D.incidencePosition (v := v)) := by
  rintro ⟨⟨⟨e, s⟩, hes⟩, i⟩ ⟨⟨⟨f, t⟩, hft⟩, j⟩ h
  change (e, i) = (f, j) at h
  have he : e = f := congrArg Prod.fst h
  have hij : i = j := congrArg Prod.snd h
  subst f
  subst j
  have hst : s = t := D.graph.endpoint_injective e (hes.trans hft.symm)
  subst t
  rfl

def testLeft {v : D.Vertex} : D.TestAt v → ℚ
  | .inl p => TreeGeometry.left D.graph.edges.length D.R D.geometryBound .plus p.val.val
  | .inr (.inl p) =>
      TreeGeometry.left D.graph.edges.length D.R D.geometryBound .minus p.val.val
  | .inr (.inr j) =>
      Geometry.jobLeft D.graph.edges.length D.R D.geometryBound D.L (D.incidencePosition j)

def testRight {v : D.Vertex} : D.TestAt v → ℚ
  | .inl p => TreeGeometry.right D.graph.edges.length D.R D.geometryBound .plus p.val.val
  | .inr (.inl p) =>
      TreeGeometry.right D.graph.edges.length D.R D.geometryBound .minus p.val.val
  | .inr (.inr j) => Geometry.baseline D.graph.edges.length D.R (D.incidencePosition j)

def testCell {v : D.Vertex} (t : D.TestAt v) : Set ℚ :=
  Set.Icc (D.testLeft t) (D.testRight t)

def testInterval {v : D.Vertex} (t : D.TestAt v) : Set ℚ :=
  Set.Ico (D.testLeft t) (D.testRight t)

theorem testLeft_lt_testRight {v : D.Vertex} (t : D.TestAt v) :
    D.testLeft t < D.testRight t := by
  rcases t with p | p | j
  · exact TreeGeometry.left_lt_right _ _ _ .plus p.val.val
  · exact TreeGeometry.left_lt_right _ _ _ .minus p.val.val
  · exact Geometry.jobLeft_lt_baseline _ _ _ _ (D.incidencePosition j)

private theorem tree_endpoints_in_root {T : UniformTree} (v : T.Node)
    (s : TreeGeometry.Side) (hT : T.branchBound ≤ D.geometryBound) :
    TreeGeometry.rootOffset s ≤
        TreeGeometry.left D.graph.edges.length D.R D.geometryBound s v.val ∧
      TreeGeometry.right D.graph.edges.length D.R D.geometryBound s v.val ≤
        TreeGeometry.rootOffset s + 1 := by
  simpa only [TreeGeometry.left_nil, TreeGeometry.right_nil] using
    TreeGeometry.prefix_endpoints D.graph.edges.length D.R D.geometryBound s
      (u := []) (v := v.val) List.nil_prefix (TreeGeometry.boundedAddress_node v hT)

theorem test_endpoints_bounds {v : D.Vertex} (t : D.TestAt v) :
    0 ≤ D.testLeft t ∧ D.testRight t ≤ 5 := by
  rcases t with p | p | j
  · have h := D.tree_endpoints_in_root p.val .plus D.plus_branch_le_geometryBound
    norm_num only [TreeGeometry.rootOffset] at h
    change 0 ≤ D.testLeft (.inl p : D.TestAt v) ∧
      D.testRight (.inl p : D.TestAt v) ≤ 1 at h
    exact ⟨h.1, by linarith [h.2]⟩
  · have h := D.tree_endpoints_in_root p.val .minus D.minus_branch_le_geometryBound
    norm_num only [TreeGeometry.rootOffset] at h
    change 4 ≤ D.testLeft (.inr (.inl p) : D.TestAt v) ∧
      D.testRight (.inr (.inl p) : D.TestAt v) ≤ 5 at h
    exact ⟨by linarith [h.1], h.2⟩
  · have hl := Geometry.one_tenth_lt_jobLeft D.graph.edges.length D.R
      D.geometryBound D.L (D.incidencePosition j)
    have hr := Geometry.job_baseline_lt_one D.graph.edges.length D.R (D.incidencePosition j)
    change 0 ≤ Geometry.jobLeft _ _ _ _ _ ∧ Geometry.baseline _ _ _ ≤ 5
    constructor <;> linarith

theorem testLeft_nonneg {v : D.Vertex} (t : D.TestAt v) : 0 ≤ D.testLeft t :=
  (D.test_endpoints_bounds t).1

theorem testRight_le_five {v : D.Vertex} (t : D.TestAt v) : D.testRight t ≤ 5 :=
  (D.test_endpoints_bounds t).2

theorem testCell_subset_range {v : D.Vertex} (t : D.TestAt v) :
    D.testCell t ⊆ Set.Icc (0 : ℚ) 5 := by
  intro x hx
  exact ⟨(D.testLeft_nonneg t).trans hx.1, hx.2.trans (D.testRight_le_five t)⟩

theorem testInterval_subset_testCell {v : D.Vertex} (t : D.TestAt v) :
    D.testInterval t ⊆ D.testCell t := fun _ hx => ⟨hx.1, hx.2.le⟩

private theorem disjoint_of_endpoint_lt {a b c d : ℚ} (h : b < c) :
    Disjoint (Set.Icc a b) (Set.Icc c d) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact (not_le_of_gt h) (hy.1.trans hx.2)

private theorem same_depth_cells_disjoint {s t : TreeGeometry.Side} {u w : List ℕ}
    (hu : u.length = D.L) (hw : w.length = D.L)
    (hbu : TreeGeometry.BoundedAddress D.geometryBound u)
    (hbw : TreeGeometry.BoundedAddress D.geometryBound w) (hne : (s, u) ≠ (t, w)) :
    Disjoint (TreeGeometry.cell D.graph.edges.length D.R D.geometryBound s u)
      (TreeGeometry.cell D.graph.edges.length D.R D.geometryBound t w) := by
  have hg := TreeGeometry.same_depth_gap D.graph.edges.length D.R D.geometryBound D.L
    hu hw hbu hbw hne
  have hp := Geometry.lambda_pos D.graph.edges.length D.R D.geometryBound D.L
  rcases hg with hg | hg
  · exact disjoint_of_endpoint_lt (by linarith)
  · exact (disjoint_of_endpoint_lt (by linarith)).symm

private theorem plusLeaf_right_lt_tenth (hplusheight : D.plus.height = D.L)
    (hL : 1 ≤ D.L) (p : D.PlusLeaf) :
    TreeGeometry.right D.graph.edges.length D.R D.geometryBound .plus p.val.val < 1 / 10 := by
  have hlength : p.val.val.length = D.L := (D.plus.length_leaf _ p.property).trans hplusheight
  have hn : p.val.val ≠ [] := by
    intro h
    rw [h] at hlength
    simp only [List.length_nil] at hlength
    omega
  have hb := TreeGeometry.nonroot_endpoints D.graph.edges.length D.R D.geometryBound .plus
    hn (TreeGeometry.boundedAddress_node p.val D.plus_branch_le_geometryBound)
  simpa only [TreeGeometry.rootOffset, zero_add] using hb.2

private theorem plusLeaf_job_disjoint (hplusheight : D.plus.height = D.L)
    (hL : 1 ≤ D.L) {v : D.Vertex} (p : D.PlusLeaf) (j : D.IncidencePosition v) :
    Disjoint (D.testCell (.inl p : D.TestAt v)) (D.testCell (.inr (.inr j))) := by
  have hp := D.plusLeaf_right_lt_tenth hplusheight hL p
  have hj := Geometry.one_tenth_lt_jobLeft D.graph.edges.length D.R D.geometryBound D.L
    (D.incidencePosition j)
  exact disjoint_of_endpoint_lt (hp.trans hj)

private theorem minusLeaf_job_disjoint {v : D.Vertex} (p : D.MinusLeaf)
    (j : D.IncidencePosition v) :
    Disjoint (D.testCell (.inr (.inl p) : D.TestAt v)) (D.testCell (.inr (.inr j))) := by
  have hp := D.tree_endpoints_in_root p.val .minus D.minus_branch_le_geometryBound
  have hj := Geometry.job_baseline_lt_one D.graph.edges.length D.R (D.incidencePosition j)
  norm_num only [TreeGeometry.rootOffset] at hp
  change 4 ≤ TreeGeometry.left D.graph.edges.length D.R D.geometryBound .minus p.val.val ∧
    _ ≤ 5 at hp
  have hgap : Geometry.baseline D.graph.edges.length D.R (D.incidencePosition j) <
      TreeGeometry.left D.graph.edges.length D.R D.geometryBound .minus p.val.val := by
    linarith [hp.1]
  exact (disjoint_of_endpoint_lt hgap).symm

theorem testCell_disjoint (hplusheight : D.plus.height = D.L)
    (hminusheight : D.minus.height = D.L) (hL : 1 ≤ D.L)
    {v : D.Vertex} {s t : D.TestAt v} (hne : s ≠ t) :
    Disjoint (D.testCell s) (D.testCell t) := by
  rcases s with p | p | j <;> rcases t with q | q | k
  · apply D.same_depth_cells_disjoint
      ((D.plus.length_leaf _ p.property).trans hplusheight)
      ((D.plus.length_leaf _ q.property).trans hplusheight)
      (TreeGeometry.boundedAddress_node p.val D.plus_branch_le_geometryBound)
      (TreeGeometry.boundedAddress_node q.val D.plus_branch_le_geometryBound)
    intro h
    have hpq : p = q := Subtype.ext (Subtype.ext (congrArg Prod.snd h))
    exact hne (congrArg Sum.inl hpq)
  · apply D.same_depth_cells_disjoint
      ((D.plus.length_leaf _ p.property).trans hplusheight)
      ((D.minus.length_leaf _ q.property).trans hminusheight)
      (TreeGeometry.boundedAddress_node p.val D.plus_branch_le_geometryBound)
      (TreeGeometry.boundedAddress_node q.val D.minus_branch_le_geometryBound)
    intro h
    have hs := congrArg Prod.fst h
    cases hs
  · exact D.plusLeaf_job_disjoint hplusheight hL p k
  · apply D.same_depth_cells_disjoint
      ((D.minus.length_leaf _ p.property).trans hminusheight)
      ((D.plus.length_leaf _ q.property).trans hplusheight)
      (TreeGeometry.boundedAddress_node p.val D.minus_branch_le_geometryBound)
      (TreeGeometry.boundedAddress_node q.val D.plus_branch_le_geometryBound)
    intro h
    have hs := congrArg Prod.fst h
    cases hs
  · apply D.same_depth_cells_disjoint
      ((D.minus.length_leaf _ p.property).trans hminusheight)
      ((D.minus.length_leaf _ q.property).trans hminusheight)
      (TreeGeometry.boundedAddress_node p.val D.minus_branch_le_geometryBound)
      (TreeGeometry.boundedAddress_node q.val D.minus_branch_le_geometryBound)
    intro h
    have hpq : p = q := Subtype.ext (Subtype.ext (congrArg Prod.snd h))
    exact hne (congrArg (fun l => Sum.inr (Sum.inl l)) hpq)
  · exact D.minusLeaf_job_disjoint p k
  · exact (D.plusLeaf_job_disjoint hplusheight hL q j).symm
  · exact (D.minusLeaf_job_disjoint q j).symm
  · apply Geometry.closedJobCell_disjoint
    intro h
    have hjk := D.incidencePosition_injective v h
    exact hne (congrArg (fun r => Sum.inr (Sum.inr r)) hjk)

theorem testCell_pairwise_disjoint (hplusheight : D.plus.height = D.L)
    (hminusheight : D.minus.height = D.L) (hL : 1 ≤ D.L) (v : D.Vertex) :
    Pairwise (fun s t : D.TestAt v => Disjoint (D.testCell s) (D.testCell t)) :=
  fun _ _ hne => D.testCell_disjoint hplusheight hminusheight hL hne

theorem testInterval_disjoint (hplusheight : D.plus.height = D.L)
    (hminusheight : D.minus.height = D.L) (hL : 1 ≤ D.L)
    {v : D.Vertex} {s t : D.TestAt v} (hne : s ≠ t) :
    Disjoint (D.testInterval s) (D.testInterval t) :=
  (D.testCell_disjoint hplusheight hminusheight hL hne).mono
    (D.testInterval_subset_testCell s) (D.testInterval_subset_testCell t)

theorem testInterval_pairwise_disjoint (hplusheight : D.plus.height = D.L)
    (hminusheight : D.minus.height = D.L) (hL : 1 ≤ D.L) (v : D.Vertex) :
    Pairwise (fun s t : D.TestAt v => Disjoint (D.testInterval s) (D.testInterval t)) :=
  fun _ _ hne => D.testInterval_disjoint hplusheight hminusheight hL hne

end BinPackingGap.InventoryData

end OAI
