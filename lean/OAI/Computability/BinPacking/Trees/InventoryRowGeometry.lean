import OAI.Computability.BinPacking.Packing.PackingCoordinates

namespace OAI

namespace BinPackingGap.InventoryData

variable (D : InventoryData)

private theorem node_right_in_root {T : UniformTree} (v : T.Node)
    (s : TreeGeometry.Side) (hT : T.branchBound ≤ D.geometryBound) :
    TreeGeometry.rootOffset s ≤
        TreeGeometry.right D.graph.edges.length D.R D.geometryBound s v.val ∧
      TreeGeometry.right D.graph.edges.length D.R D.geometryBound s v.val ≤
        TreeGeometry.rootOffset s + 1 := by
  apply TreeGeometry.nodeCell_subset_root D.graph.edges.length D.R D.geometryBound s hT v
  exact ⟨(TreeGeometry.left_lt_right _ _ _ _ _).le, le_rfl⟩

theorem rowBaseline_le_one_of_not_tm {v : D.Vertex} (r : D.RowAt v)
    (hclass : D.rowSubclass r ≠ .tm) : D.rowBaseline r ≤ 1 := by
  rcases r with t | ⟨short, j⟩
  · rcases t with ⟨node, i⟩ | ⟨node, i⟩ | i
    · have h := D.node_right_in_root node .plus D.plus_branch_le_geometryBound
      simpa only [rowBaseline, treeBaseline, TreeGeometry.rootOffset, zero_add] using h.2
    · exact (hclass rfl).elim
    · exact le_rfl
  · exact (Geometry.job_baseline_lt_one _ _ _).le

theorem rowBaseline_ge_four_of_tm {v : D.Vertex} (r : D.RowAt v)
    (hclass : D.rowSubclass r = .tm) : 4 ≤ D.rowBaseline r := by
  rcases r with t | ⟨short, j⟩
  · rcases t with ⟨node, i⟩ | ⟨node, i⟩ | i
    · cases hclass
    · exact (D.node_right_in_root node .minus D.minus_branch_le_geometryBound).1
    · cases hclass
  · cases hclass

theorem rowShort_eq_false_of_tm {v : D.Vertex} (r : D.RowAt v)
    (hclass : D.rowSubclass r = .tm) : D.rowShort r = false := by
  rcases r with t | ⟨short, j⟩
  · rfl
  · cases hclass

theorem exists_jobCopy_of_rowShort {v : D.Vertex} (r : D.RowAt v)
    (hshort : D.rowShort r = true) : ∃ j : D.JobCopy v, r = .inr (true, j) := by
  rcases r with t | ⟨short, j⟩
  · cases hshort
  · change short = true at hshort
    subst short
    exact ⟨j, rfl⟩

theorem row_zero_resources_empty {v : D.Vertex} (r : D.RowAt v)
    (hshort : D.rowShort r = false) :
    completionInterval (D.rowBaseline r) (D.rowShort r) 0 0
      (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) = ∅ := by
  rw [hshort]
  exact completionInterval_long_zero_lengths _ _

theorem row_zero_resources_job {v : D.Vertex} (r : D.RowAt v)
    (hshort : D.rowShort r = true) :
    ∃ j : D.JobCopy v, r = .inr (true, j) ∧
      D.rowPosition r = some (D.jobPosition j) ∧
      completionInterval (D.rowBaseline r) (D.rowShort r) 0 0
        (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) =
        Geometry.jobTestInterval D.graph.edges.length D.R D.geometryBound D.L
          (D.jobPosition j) := by
  obtain ⟨j, rfl⟩ := D.exists_jobCopy_of_rowShort r hshort
  refine ⟨j, rfl, rfl, ?_⟩
  exact completion_job_interval _ _ _ _ _

theorem minus_row_completion_gt_one {v w : D.Vertex} (r : D.RowAt v)
    (u : D.GlobalCopy) (l : D.LocalAt w) (hclass : D.rowSubclass r = .tm) :
    1 < completion (D.rowBaseline r) (D.rowShort r) (D.globalLength u)
      (D.localLength l) (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) := by
  apply completion_minus_geometry_gt_one
    D.graph.edges.length D.R D.geometryBound D.L
  · exact D.rowBaseline_ge_four_of_tm r hclass
  · exact D.rowShort_eq_false_of_tm r hclass
  · exact D.globalLength_le_one u
  · exact D.localLength_le_lambda_one l

theorem minus_row_not_cover_jobInterior {v w : D.Vertex} (r : D.RowAt v)
    (u : D.GlobalCopy) (l : D.LocalAt w) (hclass : D.rowSubclass r = .tm)
    (job : D.Position) :
    Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L job ∉
      completionInterval (D.rowBaseline r) (D.rowShort r) (D.globalLength u)
        (D.localLength l) (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) := by
  intro hmem
  have hh := D.minus_row_completion_gt_one r u l hclass
  have hj := (Geometry.closedJobCell_bounds
    (Geometry.jobInterior_mem_closedJobCell D.graph.edges.length D.R
      D.geometryBound D.L job)).2
  exact (not_le_of_gt (hj.trans hh)) hmem.1

theorem plus_row_not_cover_minus_side {v w : D.Vertex} (r : D.RowAt v)
    (u : D.GlobalCopy) (l : D.LocalAt w) (hclass : D.rowSubclass r ≠ .tm)
    {a : ℚ} (ha : 4 ≤ a) :
    a ∉ completionInterval (D.rowBaseline r) (D.rowShort r) (D.globalLength u)
      (D.localLength l) (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) := by
  apply not_mem_plus_completionInterval
  · exact D.rowBaseline_le_one_of_not_tm r hclass
  · linarith

end BinPackingGap.InventoryData

end OAI
