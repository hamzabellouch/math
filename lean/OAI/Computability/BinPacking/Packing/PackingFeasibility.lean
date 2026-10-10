import OAI.Computability.BinPacking.Inventory.InventoryCoverage
import OAI.Computability.BinPacking.Trees.KeyGeometry

namespace OAI

noncomputable section

namespace BinPackingGap
namespace PackingCounts

open scoped BigOperators

variable {D : InventoryData} {I : Instance} {b : ℕ}

theorem good_selected_labels (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.goodTuplesAt p (subclass e) (label e) v) (r : Role) :
    label e (p.itemAtRole (subclass e) t r) = tableRoleLabel v v v r := by
  cases r with
  | x =>
      simpa only [selected_row_label, tableRoleLabel] using
        congrArg some (good_row_vertex p e v t ht)
  | anchor =>
      simpa only [selected_anchor_label, tableRoleLabel] using
        congrArg some (good_anchor_vertex p e v t ht)
  | «global» =>
      change D.itemLabel (e.symm (p.itemAtRole (subclass e) t .«global»)) = none
      rw [← roleCopy_item p e t .«global», e.symm_apply_apply]
      rfl
  | «local» =>
      simpa only [selected_local_label, tableRoleLabel] using
        congrArg some (good_local_vertex p e v t ht)
  | flag =>
      change D.itemLabel (e.symm (p.itemAtRole (subclass e) t .flag)) = none
      rw [← roleCopy_item p e t .flag, e.symm_apply_apply]
      rfl

@[simp] theorem selected_itemCoordinate (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (r : Role) :
    D.itemCoordinate (e.symm (p.itemAtRole (subclass e) t r)) =
      D.itemCoordinate ⟨r, roleCopy p e t r⟩ := by
  rw [← roleCopy_item p e t r]
  simp only [Equiv.symm_apply_apply]

theorem good_coordinate_nonpos (p : Packing I b) (e : D.Item ≃ I.Item)
    (hsize : ∀ i, I.size i =
      encodedSize (subclass e i) (label e i) (D.itemCoordinate (e.symm i)))
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.goodTuplesAt p (subclass e) (label e) v) :
    D.rowCoordinate (rowCopy p e t).2 + D.anchorCoordinate (anchorCopy p e t).2 +
      D.globalCoordinate (globalCopy p e t) + D.localCoordinate (localCopy p e t).2 ≤ 0 := by
  have h := p.table_coordinate_nonpos_of_same_label (subclass e) (label e)
    (fun i => D.itemCoordinate (e.symm i)) hsize t v (good_selected_labels p e v t ht)
  simp only [selected_itemCoordinate] at h
  rw [Role.sum_univ] at h
  have hx (x : Σ v : D.Vertex, D.RowAt v) :
      D.itemCoordinate ⟨.x, x⟩ = D.rowCoordinate x.2 := by
    cases x
    rfl
  have ha (a : Σ v : D.Vertex, D.AnchorAt v) :
      D.itemCoordinate ⟨.anchor, a⟩ = D.anchorCoordinate a.2 := by
    cases a
    rfl
  have hl (l : Σ v : D.Vertex, D.LocalAt v) :
      D.itemCoordinate ⟨.«local», l⟩ = D.localCoordinate l.2 := by
    cases l
    rfl
  rw [hx (rowCopy p e t), ha (anchorCopy p e t), hl (localCopy p e t)] at h
  simpa only [InventoryData.itemCoordinate, add_zero] using h

private theorem main_anchor_of_subclass (a : Σ v : D.Vertex, D.AnchorAt v)
    (h : D.itemSubclass ⟨.anchor, a⟩ = .z) :
    ∃ z : D.MBase a.1, a.2 = .inl z := by
  rcases a with ⟨v, z | j⟩
  · exact ⟨z, rfl⟩
  · simp [InventoryData.itemSubclass] at h

private theorem globalCoordinate_of_not_w (u : D.GlobalCopy)
    (h : D.itemSubclass ⟨.«global», u⟩ ≠ .w) :
    D.globalCoordinate u = -D.globalLength u := by
  rcases u with ⟨species, i⟩
  cases species with
  | up one => rfl
  | um one => rfl
  | edge edge permit => exact (h rfl).elim

theorem main_anchor_copy (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (hpat : p.tablePattern (subclass e) t ≠ .edgeJob) :
    ∃ z : D.MBase (anchorCopy p e t).1, (anchorCopy p e t).2 = .inl z := by
  apply main_anchor_of_subclass
  have h := roleCopy_subclass p e t .anchor
  cases hp : p.tablePattern (subclass e) t <;> simp_all [patternSubclass]

theorem main_globalCoordinate (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (hpat : p.tablePattern (subclass e) t ≠ .edgeJob) :
    D.globalCoordinate (globalCopy p e t) = -D.globalLength (globalCopy p e t) := by
  apply globalCoordinate_of_not_w
  have h := roleCopy_subclass p e t .«global»
  cases hp : p.tablePattern (subclass e) t <;> simp_all [patternSubclass]

theorem main_completion_le_deadline (p : Packing I b) (e : D.Item ≃ I.Item)
    (hsize : ∀ i, I.size i =
      encodedSize (subclass e i) (label e i) (D.itemCoordinate (e.symm i)))
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v) :
    ∃ z : D.MBase (anchorCopy p e t).1,
      (anchorCopy p e t).2 = .inl z ∧ tupleFinish p e t ≤ D.deadline z := by
  have hpat := ((Coverage.mem_mainTuplesAt p (subclass e) (label e) v t).mp ht).2.2
  have hgood := Coverage.mainTuplesAt_subset_good p (subclass e) (label e) v ht
  have h := good_coordinate_nonpos p e hsize v t hgood
  obtain ⟨z, hz⟩ := main_anchor_copy p e t hpat
  refine ⟨z, hz, ?_⟩
  have ha : D.anchorCoordinate (anchorCopy p e t).2 = -D.deadline z := by
    rw [hz]
    rfl
  rw [ha, main_globalCoordinate p e t hpat] at h
  change D.rowCoordinate (rowCopy p e t).2 + -D.deadline z +
    -D.globalLength (globalCopy p e t) + -D.localLength (localCopy p e t).2 ≤ 0 at h
  have rearrange (x deadline globalLen localLen : ℚ)
      (hh : x + -deadline + -globalLen + -localLen ≤ 0) :
      x - globalLen - localLen ≤ deadline := by linarith
  exact rearrange (D.rowCoordinate (rowCopy p e t).2) (D.deadline z)
    (D.globalLength (globalCopy p e t)) (D.localLength (localCopy p e t).2) h

theorem main_completion_le_selected_deadline (p : Packing I b) (e : D.Item ≃ I.Item)
    (hsize : ∀ i, I.size i =
      encodedSize (subclass e i) (label e i) (D.itemCoordinate (e.symm i)))
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v) :
    tupleFinish p e t ≤
      InventoryCoverage.anchorDeadline e (p.itemAtRole (subclass e) t .anchor) := by
  obtain ⟨z, hz, hfinish⟩ := main_completion_le_deadline p e hsize v t ht
  have hcopy : anchorCopy p e t = ⟨(anchorCopy p e t).1, .inl z⟩ := by
    conv_lhs => rw [← Sigma.eta (anchorCopy p e t)]
    rw [hz]
  rw [InventoryCoverage.anchorDeadline_selected_of_deadline p e t _ z hcopy]
  exact hfinish

private theorem job_row_of_subclass (a : Σ v : D.Vertex, D.RowAt v)
    (h : D.itemSubclass ⟨.x, a⟩ = .s) :
    ∃ short : Bool, ∃ j : D.JobCopy a.1, a.2 = .inr (short, j) := by
  rcases a with ⟨v, row | ⟨short, j⟩⟩
  · rcases row with plus | (minus | padding) <;>
      simp [InventoryData.itemSubclass, InventoryData.rowSubclass,
        InventoryData.treeSubclass] at h
  · exact ⟨short, j, rfl⟩

private theorem key_anchor_of_subclass (a : Σ v : D.Vertex, D.AnchorAt v)
    (h : D.itemSubclass ⟨.anchor, a⟩ = .y) :
    ∃ j : D.JobCopy a.1, a.2 = .inr j := by
  rcases a with ⟨v, z | j⟩
  · simp [InventoryData.itemSubclass] at h
  · exact ⟨j, rfl⟩

private theorem edge_global_of_subclass (u : D.GlobalCopy)
    (h : D.itemSubclass ⟨.«global», u⟩ = .w) :
    ∃ edge : D.Edge, ∃ permit : Bool, ∃ i : Fin (D.globalStock (.edge edge permit)),
      u = ⟨.edge edge permit, i⟩ := by
  rcases u with ⟨species, i⟩
  cases species with
  | up one => simp [InventoryData.itemSubclass] at h
  | um one => simp [InventoryData.itemSubclass] at h
  | edge edge permit => exact ⟨edge, permit, i, rfl⟩

private theorem edge_local_of_subclass (a : Σ v : D.Vertex, D.LocalAt v)
    (h : D.itemSubclass ⟨.«local», a⟩ = .dg) :
    ∃ j : D.JobCopy a.1, a.2 = .inr j := by
  rcases a with ⟨v, main | j⟩
  · simp [InventoryData.itemSubclass] at h
  · exact ⟨j, rfl⟩

structure EdgeTupleData (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) where
  short : Bool
  row : D.JobCopy (rowCopy p e t).1
  key : D.JobCopy (anchorCopy p e t).1
  localJob : D.JobCopy (localCopy p e t).1
  edge : D.Edge
  permit : Bool
  globalIndex : Fin (D.globalStock (.edge edge permit))
  row_eq : (rowCopy p e t).2 = .inr (short, row)
  anchor_eq : (anchorCopy p e t).2 = .inr key
  local_eq : (localCopy p e t).2 = .inr localJob
  global_eq : globalCopy p e t = ⟨.edge edge permit, globalIndex⟩

theorem edgeTupleData_nonempty (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (hpat : p.tablePattern (subclass e) t = .edgeJob) :
    Nonempty (EdgeTupleData p e t) := by
  have hx : D.itemSubclass ⟨.x, rowCopy p e t⟩ = .s := by
    simpa only [hpat, patternSubclass] using roleCopy_subclass p e t .x
  have ha : D.itemSubclass ⟨.anchor, anchorCopy p e t⟩ = .y := by
    simpa only [hpat, patternSubclass] using roleCopy_subclass p e t .anchor
  have hu : D.itemSubclass ⟨.«global», globalCopy p e t⟩ = .w := by
    simpa only [hpat, patternSubclass] using roleCopy_subclass p e t .«global»
  have hl : D.itemSubclass ⟨.«local», localCopy p e t⟩ = .dg := by
    simpa only [hpat, patternSubclass] using roleCopy_subclass p e t .«local»
  obtain ⟨short, row, hrow⟩ := job_row_of_subclass _ hx
  obtain ⟨key, hkey⟩ := key_anchor_of_subclass _ ha
  obtain ⟨edge, permit, i, hglobal⟩ := edge_global_of_subclass _ hu
  obtain ⟨localJob, hlocal⟩ := edge_local_of_subclass _ hl
  exact ⟨⟨short, row, key, localJob, edge, permit, i, hrow, hkey, hlocal, hglobal⟩⟩

namespace EdgeTupleData

variable {p : Packing I b} {e : D.Item ≃ I.Item} {t : p.TableBin (subclass e)}

def expression (w : EdgeTupleData p e t) : ℚ :=
  Geometry.keyExpression D.graph.edges.length D.R D.geometryBound D.L
    (D.jobPosition w.row) (D.jobPosition w.key) w.edge (!w.permit) w.short

theorem expression_eq_coordinates (w : EdgeTupleData p e t) :
    w.expression =
      D.rowCoordinate (rowCopy p e t).2 + D.anchorCoordinate (anchorCopy p e t).2 +
        D.globalCoordinate (globalCopy p e t) + D.localCoordinate (localCopy p e t).2 := by
  rw [w.row_eq, w.anchor_eq, w.global_eq, w.local_eq]
  unfold expression
  rw [Geometry.keyExpression_eq_coordinates]
  simp only [InventoryData.rowCoordinate, InventoryData.rowBaseline, InventoryData.rowShort,
    InventoryData.anchorCoordinate, InventoryData.globalCoordinate,
    InventoryData.localCoordinate, InventoryData.localLength, neg_zero, add_zero]
  cases w.permit <;> cases w.short <;> simp

theorem feasible (w : EdgeTupleData p e t)
    (hsize : ∀ i, I.size i =
      encodedSize (subclass e i) (label e i) (D.itemCoordinate (e.symm i)))
    (v : D.Vertex) (ht : t ∈ Coverage.goodTuplesAt p (subclass e) (label e) v) :
    w.expression ≤ 0 := by
  rw [w.expression_eq_coordinates]
  exact good_coordinate_nonpos p e hsize v t ht

theorem row_order (w : EdgeTupleData p e t) (h : w.expression ≤ 0) :
    Geometry.posLE (D.jobPosition w.row) (D.jobPosition w.key) :=
  Geometry.row_order_of_key_feasible h

theorem edge_order (w : EdgeTupleData p e t) (h : w.expression ≤ 0) :
    w.edge ≤ (D.jobPosition w.key).1 :=
  Geometry.edge_order_of_key_feasible h

theorem exact_long_resource (w : EdgeTupleData p e t) (h : w.expression ≤ 0)
    (hpos : D.jobPosition w.row = D.jobPosition w.key) (hlong : w.short = false) :
    w.edge < (D.jobPosition w.key).1 ∨
      (w.edge = (D.jobPosition w.key).1 ∧ w.permit = true) := by
  have h' : Geometry.keyExpression D.graph.edges.length D.R D.geometryBound D.L
      (D.jobPosition w.key) (D.jobPosition w.key) w.edge (!w.permit) false ≤ 0 := by
    simpa only [expression, hpos, hlong] using h
  have hresource := Geometry.exact_long_key_resource (D.jobPosition w.key) w.edge
    (!w.permit) h'
  cases hp : w.permit <;> simpa [hp] using hresource

end EdgeTupleData

theorem edge_tuple_feasible (p : Packing I b) (e : D.Item ≃ I.Item)
    (hsize : ∀ i, I.size i =
      encodedSize (subclass e i) (label e i) (D.itemCoordinate (e.symm i)))
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.edgeTuplesAt p (subclass e) (label e) v) :
    ∃ w : EdgeTupleData p e t, w.expression ≤ 0 ∧
      Geometry.posLE (D.jobPosition w.row) (D.jobPosition w.key) ∧
        w.edge ≤ (D.jobPosition w.key).1 := by
  have hpat := ((Coverage.mem_edgeTuplesAt p (subclass e) (label e) v t).mp ht).2.2
  obtain ⟨w⟩ := edgeTupleData_nonempty p e t hpat
  have hf := w.feasible hsize v
    (Coverage.edgeTuplesAt_subset_good p (subclass e) (label e) v ht)
  exact ⟨w, hf, w.row_order hf, w.edge_order hf⟩

theorem edge_selected_baseline_le (p : Packing I b) (e : D.Item ≃ I.Item)
    (hsize : ∀ i, I.size i =
      encodedSize (subclass e i) (label e i) (D.itemCoordinate (e.symm i)))
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.edgeTuplesAt p (subclass e) (label e) v) :
    InventoryCoverage.rowBaseline e (p.itemAtRole (subclass e) t .x) ≤
      InventoryCoverage.keyBaseline e (p.itemAtRole (subclass e) t .anchor) := by
  obtain ⟨w, _, hrow, _⟩ := edge_tuple_feasible p e hsize v t ht
  have hcopy : anchorCopy p e t = ⟨(anchorCopy p e t).1, .inr w.key⟩ := by
    conv_lhs => rw [← Sigma.eta (anchorCopy p e t)]
    rw [w.anchor_eq]
  rw [InventoryCoverage.rowBaseline_selected,
    InventoryCoverage.keyBaseline_selected_of_key p e t _ w.key hcopy, w.row_eq]
  exact Geometry.baseline_le_iff.mpr hrow

end PackingCounts
end BinPackingGap

end

end OAI
