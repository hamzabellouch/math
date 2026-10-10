import OAI.Computability.BinPacking.Inventory.InventoryPrefixConservation
import OAI.Computability.BinPacking.Inventory.LocalCompletionCoverage
import OAI.Computability.BinPacking.Machines.PackingJobCoverage
import OAI.Computability.BinPacking.Packing.PackingFeasibility

namespace OAI

noncomputable section

namespace BinPackingGap

namespace InventoryCoverage

variable {D : InventoryData} {I : Instance} {b : ℕ}

theorem coveringTuplesAt_eq (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (a : ℚ) :
    Coverage.coveringTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) (PackingCounts.tupleFinish p e) a =
      PackingCounts.tupleCovering p e v a := by
  unfold Coverage.coveringTuplesAt PackingCounts.tupleCovering
  apply Finset.filter_congr
  intro t _
  rw [rowBaseline_selected p e t]
  rfl

theorem shortMainAt_eq (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (r : D.Position) :
    Coverage.currentShortMainAt p (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) (rowShort e) (Geometry.baseline D.graph.edges.length D.R r) =
      PackingCounts.shortMainAt p e v r := by
  unfold Coverage.currentShortMainAt PackingCounts.shortMainAt
  apply Finset.filter_congr
  intro t _
  rw [rowBaseline_selected p e t, rowShort_selected p e t]
  rfl

end InventoryCoverage

namespace InventoryData

variable (D : InventoryData)

theorem test_coverage {b c : ℕ}
    (hplusheight : D.plus.height = D.L) (hminusheight : D.minus.height = D.L)
    (hL : 1 ≤ D.L) (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c)
    (v : D.Vertex) (t : D.TestAt v) (a : ℚ) (ha : a ∈ D.testInterval t) :
    D.d ≤ (PackingCounts.tupleCovering p D.itemEquiv v a).card + 6 * lossAllowance c := by
  classical
  have hbad := D.badAnchorsAt_card_le hk p hb v
  have horder := PackingCounts.edge_selected_baseline_le p D.itemEquiv
    D.packingInstance_size_eq v
  have hle : ∀ u ∈ Coverage.mainTuplesAt p (PackingCounts.subclass D.itemEquiv) (PackingCounts.label D.itemEquiv) v,
      PackingCounts.tupleFinish p D.itemEquiv u ≤
        InventoryCoverage.rowBaseline D.itemEquiv (p.itemAtRole (PackingCounts.subclass D.itemEquiv) u .x) := by
    intro u _
    simpa only [InventoryCoverage.rowBaseline_selected, PackingCounts.tupleBaseline] using
      PackingCounts.tupleFinish_le_baseline p D.itemEquiv u
  have hfeasible := PackingCounts.main_completion_le_selected_deadline p D.itemEquiv
    D.packingInstance_size_eq v
  have hdeficit := InventoryCoverage.actual_deadline_deficit_bound p D.itemEquiv v a
    (lossAllowance c) (PackingCounts.tupleFinish p D.itemEquiv) hbad horder hle hfeasible
  rw [D.deadline_prefix_at_test hplusheight hminusheight hL v t a ha,
    InventoryCoverage.coveringTuplesAt_eq] at hdeficit
  change (InventoryCoverage.originalBaselinePrefix D v a).card + D.d ≤
    (InventoryCoverage.originalBaselinePrefix D v a).card +
      (PackingCounts.tupleCovering p D.itemEquiv v a).card + 6 * lossAllowance c at hdeficit
  omega

def longMatchesAt {b : ℕ} (p : Packing D.packingInstance b)
    (v : D.Vertex) (r : D.IncidencePosition v) : ℕ :=
  (Coverage.currentLongEdgeAt p D.encodedSubclass D.encodedLabel v
    (InventoryCoverage.rowBaseline D.itemEquiv) (InventoryCoverage.keyBaseline D.itemEquiv)
    (InventoryCoverage.rowShort D.itemEquiv)
    (Geometry.baseline D.graph.edges.length D.R (D.incidencePosition r))).card

theorem long_matches_at_nonexcluded {b c : ℕ}
    (hplusheight : D.plus.height = D.L) (hminusheight : D.minus.height = D.L)
    (hL : 1 ≤ D.L) (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c)
    (v : D.Vertex) (r : D.IncidencePosition v)
    (hr : D.incidencePosition r ∉ PackingCounts.excludedAt p D.itemEquiv v) :
    D.d ≤ D.longMatchesAt p v r + PackingCounts.xplus p D.itemEquiv v + 9 * lossAllowance c := by
  classical
  let a := Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L (D.incidencePosition r)
  let finish := PackingCounts.tupleFinish p D.itemEquiv
  have hbad := D.badAnchorsAt_card_le hk p hb v
  have horder := PackingCounts.edge_selected_baseline_le p D.itemEquiv
    D.packingInstance_size_eq v
  have hle : ∀ u ∈ Coverage.mainTuplesAt p (PackingCounts.subclass D.itemEquiv) (PackingCounts.label D.itemEquiv) v,
      finish u ≤ InventoryCoverage.rowBaseline D.itemEquiv
        (p.itemAtRole (PackingCounts.subclass D.itemEquiv) u .x) := by
    intro u _
    simpa only [finish, InventoryCoverage.rowBaseline_selected, PackingCounts.tupleBaseline] using
      PackingCounts.tupleFinish_le_baseline p D.itemEquiv u
  have hfeasible := PackingCounts.main_completion_le_selected_deadline p D.itemEquiv
    D.packingInstance_size_eq v
  have hpartition := Coverage.completion_prefix_decomposition p (PackingCounts.subclass D.itemEquiv)
    (PackingCounts.label D.itemEquiv) v (InventoryCoverage.rowBaseline D.itemEquiv) finish hle a
  have hdeadline := Coverage.deadline_prefix_le_completion_add_loss p (PackingCounts.subclass D.itemEquiv)
    (PackingCounts.label D.itemEquiv) v (InventoryCoverage.anchorDeadline D.itemEquiv) finish a
    (lossAllowance c) hbad hfeasible
  have ha : a ∈ D.testInterval (.inr (.inr r) : D.TestAt v) :=
    Geometry.jobInterior_mem_jobTestInterval D.graph.edges.length D.R D.geometryBound D.L
      (D.incidencePosition r)
  rw [InventoryCoverage.deadlinePrefix_card,
    D.deadline_prefix_at_test hplusheight hminusheight hL v (.inr (.inr r)) a ha] at hdeadline
  have hbase := InventoryCoverage.actual_displaced_job_prefix_le p D.itemEquiv v r
    (lossAllowance c) hbad horder
  have hupper : (Coverage.coveringTuplesAt p (PackingCounts.subclass D.itemEquiv) (PackingCounts.label D.itemEquiv) v
      (InventoryCoverage.rowBaseline D.itemEquiv) finish a).card ≤
      PackingCounts.xplus p D.itemEquiv v +
      (Coverage.currentShortMainAt p (PackingCounts.subclass D.itemEquiv) (PackingCounts.label D.itemEquiv) v
        (InventoryCoverage.rowBaseline D.itemEquiv) (InventoryCoverage.rowShort D.itemEquiv)
        (Geometry.baseline D.graph.edges.length D.R (D.incidencePosition r))).card := by
    simpa only [finish, a, InventoryCoverage.coveringTuplesAt_eq,
      InventoryCoverage.shortMainAt_eq] using
      PackingCounts.nonexcluded_coverage_upper p D.itemEquiv v (D.incidencePosition r) hr
  have hcorrection := CoverageCounts.displaced_short_correction hpartition hdeadline hbase hupper
  exact InventoryCoverage.actual_current_long_matches_from_correction p D.itemEquiv v r
    (lossAllowance c) (PackingCounts.xplus p D.itemEquiv v) hbad horder hcorrection

end InventoryData
end BinPackingGap

end

end OAI
