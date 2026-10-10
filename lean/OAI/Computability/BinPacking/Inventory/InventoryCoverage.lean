import Mathlib.Algebra.BigOperators.Ring.Finset
import OAI.Computability.BinPacking.Packing.PackingCoordinates

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinPackingGap
namespace InventoryCoverage

variable {D : InventoryData} {I : Instance} {b : ℕ}

def itemRowBaseline (D : InventoryData) : D.Item → ℚ
  | ⟨.x, ⟨_, r⟩⟩ => D.rowBaseline r
  | _ => 0

def itemRowShort (D : InventoryData) : D.Item → Bool
  | ⟨.x, ⟨_, r⟩⟩ => D.rowShort r
  | _ => false

def itemKeyBaseline (D : InventoryData) : D.Item → ℚ
  | ⟨.anchor, ⟨_, .inr j⟩⟩ => Geometry.baseline D.graph.edges.length D.R (D.jobPosition j)
  | _ => 0

def itemDeadline (D : InventoryData) : D.Item → ℚ
  | ⟨.anchor, ⟨_, .inl z⟩⟩ => D.deadline z
  | _ => 0

def rowBaseline (e : D.Item ≃ I.Item) : I.Item → ℚ := itemRowBaseline D ∘ e.symm

def rowShort (e : D.Item ≃ I.Item) : I.Item → Bool := itemRowShort D ∘ e.symm

def keyBaseline (e : D.Item ≃ I.Item) : I.Item → ℚ := itemKeyBaseline D ∘ e.symm

def anchorDeadline (e : D.Item ≃ I.Item) : I.Item → ℚ := itemDeadline D ∘ e.symm

@[simp] theorem rowBaseline_selected (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (PackingCounts.subclass e)) :
    rowBaseline e (p.itemAtRole (PackingCounts.subclass e) t .x) =
      D.rowBaseline (PackingCounts.rowCopy p e t).2 := by
  rw [← PackingCounts.roleCopy_item p e t .x]
  change itemRowBaseline D (e.symm (e ⟨.x, PackingCounts.rowCopy p e t⟩)) = _
  rw [e.symm_apply_apply]
  rfl

@[simp] theorem rowShort_selected (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (PackingCounts.subclass e)) :
    rowShort e (p.itemAtRole (PackingCounts.subclass e) t .x) =
      D.rowShort (PackingCounts.rowCopy p e t).2 := by
  rw [← PackingCounts.roleCopy_item p e t .x]
  change itemRowShort D (e.symm (e ⟨.x, PackingCounts.rowCopy p e t⟩)) = _
  rw [e.symm_apply_apply]
  rfl

theorem keyBaseline_selected_of_key (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (PackingCounts.subclass e)) (v : D.Vertex) (j : D.JobCopy v)
    (hcopy : PackingCounts.anchorCopy p e t = ⟨v, .inr j⟩) :
    keyBaseline e (p.itemAtRole (PackingCounts.subclass e) t .anchor) =
      Geometry.baseline D.graph.edges.length D.R (D.jobPosition j) := by
  rw [← PackingCounts.roleCopy_item p e t .anchor]
  change itemKeyBaseline D (e.symm (e ⟨.anchor, PackingCounts.anchorCopy p e t⟩)) = _
  rw [e.symm_apply_apply, hcopy]
  rfl

theorem anchorDeadline_selected_of_deadline (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (PackingCounts.subclass e)) (v : D.Vertex) (z : D.MBase v)
    (hcopy : PackingCounts.anchorCopy p e t = ⟨v, .inl z⟩) :
    anchorDeadline e (p.itemAtRole (PackingCounts.subclass e) t .anchor) = D.deadline z := by
  rw [← PackingCounts.roleCopy_item p e t .anchor]
  change itemDeadline D (e.symm (e ⟨.anchor, PackingCounts.anchorCopy p e t⟩)) = _
  rw [e.symm_apply_apply, hcopy]
  rfl

theorem rowShort_implies_job (e : D.Item ≃ I.Item) (i : I.Item)
    (h : rowShort e i = true) : PackingCounts.subclass e i = .s := by
  let x := e.symm i
  change itemRowShort D x = true at h
  change D.itemSubclass x = .s
  rcases x with ⟨role, copy⟩
  cases role with
  | x =>
      rcases copy with ⟨v, tree | ⟨short, job⟩⟩
      · cases h
      · rfl
  | anchor => cases h
  | «global» => cases h
  | «local» => cases h
  | flag => cases h

private theorem treeSubclass_ne_s (t : D.TreeRow) : D.treeSubclass t ≠ .s := by
  rcases t with p | (m | pad) <;> simp [InventoryData.treeSubclass]

private theorem treeSubclass_tree (t : D.TreeRow) :
    D.treeSubclass t = .tp ∨ D.treeSubclass t = .tm := by
  rcases t with p | (m | pad)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

def treePrefix (D : InventoryData) (a : ℚ) : Finset D.TreeRow :=
  Finset.univ.filter fun r => D.treeBaseline r ≤ a

def jobPrefix (D : InventoryData) (v : D.Vertex) (a : ℚ) : Finset (D.JobCopy v) :=
  Finset.univ.filter fun j => Geometry.baseline D.graph.edges.length D.R (D.jobPosition j) ≤ a

def originalBaselinePrefix (D : InventoryData) (v : D.Vertex) (a : ℚ) :
    Finset (D.MBase v) := Finset.univ.filter fun z => D.mainBaseline z ≤ a

def jobsAt (D : InventoryData) (v : D.Vertex) (current : ℚ) : Finset (D.JobCopy v) :=
  Finset.univ.filter fun j =>
    Geometry.baseline D.graph.edges.length D.R (D.jobPosition j) = current

private theorem card_filter_transport {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (P : β → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = (Finset.univ.filter fun x => P (e x)).card := by
  exact (Finset.card_bijective (s := Finset.univ.filter fun x => P (e x))
    (t := Finset.univ.filter P) e e.bijective (fun _ => by simp)).symm

theorem jobRowPrefix_card (e : D.Item ≃ I.Item) (v : D.Vertex) (a : ℚ) :
    (Coverage.jobRowPrefixAt (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) a).card = 2 * (jobPrefix D v a).card := by
  classical
  unfold Coverage.jobRowPrefixAt
  rw [card_filter_transport e]
  simp only [jobPrefix, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp [ite_and, -Finset.sum_boole, PackingCounts.subclass, PackingCounts.label, rowBaseline, itemRowBaseline,
    InventoryData.itemSubclass, InventoryData.itemLabel, InventoryData.RoleCopies,
    InventoryData.rowSubclass, InventoryData.rowBaseline, treeSubclass_ne_s,
    Fintype.sum_sigma,
    Role.sum_univ, Fintype.sum_sum_type, Fintype.sum_prod_type, two_mul]

theorem treeRowPrefix_card (e : D.Item ≃ I.Item) (v : D.Vertex) (a : ℚ) :
    (Coverage.treeRowPrefixAt (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) a).card = (treePrefix D a).card := by
  classical
  unfold Coverage.treeRowPrefixAt
  rw [card_filter_transport e]
  simp only [treePrefix, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp [ite_and, -Finset.sum_boole, PackingCounts.subclass, PackingCounts.label, rowBaseline, itemRowBaseline,
    InventoryData.itemSubclass, InventoryData.itemLabel, InventoryData.RoleCopies,
    InventoryData.rowSubclass, InventoryData.rowBaseline, treeSubclass_tree,
    Fintype.sum_sigma,
    Role.sum_univ, Fintype.sum_sum_type, Fintype.sum_prod_type]

theorem keyPrefix_card (e : D.Item ≃ I.Item) (v : D.Vertex) (a : ℚ) :
    (Coverage.keyPrefixAt (PackingCounts.subclass e) (PackingCounts.label e) v
      (keyBaseline e) a).card = (jobPrefix D v a).card := by
  classical
  unfold Coverage.keyPrefixAt
  rw [card_filter_transport e]
  simp only [jobPrefix, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp [ite_and, -Finset.sum_boole, PackingCounts.subclass, PackingCounts.label, keyBaseline, itemKeyBaseline,
    InventoryData.itemSubclass, InventoryData.itemLabel, InventoryData.RoleCopies,
    InventoryData.rowSubclass, InventoryData.treeSubclass, InventoryData.TreeRow,
    Fintype.sum_sigma,
    Role.sum_univ, Fintype.sum_sum_type, Fintype.sum_prod_type]

theorem deadlinePrefix_card (e : D.Item ≃ I.Item) (v : D.Vertex) (a : ℚ) :
    (Coverage.deadlinePrefixAt (PackingCounts.subclass e) (PackingCounts.label e) v
      (anchorDeadline e) a).card =
      (Finset.univ.filter fun z : D.MBase v => D.deadline z ≤ a).card := by
  classical
  unfold Coverage.deadlinePrefixAt
  rw [card_filter_transport e]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp [ite_and, -Finset.sum_boole, PackingCounts.subclass, PackingCounts.label, anchorDeadline, itemDeadline,
    InventoryData.itemSubclass, InventoryData.itemLabel, InventoryData.RoleCopies,
    InventoryData.rowSubclass, InventoryData.treeSubclass, InventoryData.TreeRow,
    Fintype.sum_sigma,
    Role.sum_univ, Fintype.sum_sum_type, Fintype.sum_prod_type]

theorem originalBaselinePrefix_card (D : InventoryData) (v : D.Vertex) (a : ℚ) :
    (originalBaselinePrefix D v a).card = (treePrefix D a).card + (jobPrefix D v a).card := by
  classical
  have hsplit : originalBaselinePrefix D v a =
      (treePrefix D a).disjSum (jobPrefix D v a) := by
    ext z
    cases z <;>
      simp only [originalBaselinePrefix, treePrefix, jobPrefix, Finset.mem_filter,
        Finset.mem_univ, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum, true_and] <;>
      rfl
  rw [hsplit, Finset.card_disjSum]

theorem currentKeyItems_card (e : D.Item ≃ I.Item) (v : D.Vertex) (current : ℚ) :
    (Coverage.currentKeyItemsAt (PackingCounts.subclass e) (PackingCounts.label e) v
      (keyBaseline e) current).card = (jobsAt D v current).card := by
  classical
  unfold Coverage.currentKeyItemsAt
  rw [card_filter_transport e]
  simp only [jobsAt, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp [ite_and, -Finset.sum_boole, PackingCounts.subclass, PackingCounts.label, keyBaseline, itemKeyBaseline,
    InventoryData.itemSubclass, InventoryData.itemLabel, InventoryData.RoleCopies,
    InventoryData.rowSubclass, InventoryData.treeSubclass, InventoryData.TreeRow,
    Fintype.sum_sigma,
    Role.sum_univ, Fintype.sum_sum_type, Fintype.sum_prod_type]

theorem currentShortItems_card (e : D.Item ≃ I.Item) (v : D.Vertex) (current : ℚ) :
    (Coverage.currentShortItemsAt (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) (rowShort e) current).card = (jobsAt D v current).card := by
  classical
  unfold Coverage.currentShortItemsAt
  rw [card_filter_transport e]
  simp only [jobsAt, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp [ite_and, -Finset.sum_boole, PackingCounts.subclass, PackingCounts.label, rowBaseline, rowShort,
    itemRowBaseline, itemRowShort, InventoryData.itemSubclass, InventoryData.itemLabel,
    InventoryData.RoleCopies, InventoryData.rowSubclass, InventoryData.rowBaseline,
    InventoryData.rowShort, treeSubclass_ne_s,
    Fintype.sum_sigma,
    Role.sum_univ, Fintype.sum_sum_type, Fintype.sum_prod_type]

def positionOf (D : InventoryData) {v : D.Vertex} (r : D.IncidencePosition v) : D.Position :=
  D.incidencePosition r

theorem positionOf_injective (D : InventoryData) (v : D.Vertex) :
    Function.Injective (positionOf D (v := v)) :=
  D.incidencePosition_injective v

theorem job_baseline_eq_iff (D : InventoryData) (v : D.Vertex)
    (j : D.JobCopy v) (r : D.IncidencePosition v) :
    Geometry.baseline D.graph.edges.length D.R (D.jobPosition j) =
      Geometry.baseline D.graph.edges.length D.R (positionOf D r) ↔ j.1 = r := by
  rw [Geometry.baseline_eq_iff]
  change positionOf D j.1 = positionOf D r ↔ j.1 = r
  exact (positionOf_injective D v).eq_iff

theorem jobsAt_position_card (D : InventoryData) (v : D.Vertex)
    (r : D.IncidencePosition v) :
    (jobsAt D v (Geometry.baseline D.graph.edges.length D.R (positionOf D r))).card = D.d := by
  classical
  have heq : jobsAt D v (Geometry.baseline D.graph.edges.length D.R (positionOf D r)) =
      ({r} : Finset (D.IncidencePosition v)).product (Finset.univ : Finset (Fin D.d)) := by
    ext ⟨s, j⟩
    simp only [jobsAt, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.product_eq_sprod, Finset.mem_product, Finset.mem_singleton, and_true]
    exact job_baseline_eq_iff D v (s, j) r
  rw [heq]
  simp

theorem actual_displaced_baseline_prefix_le
    (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex) (a : ℚ)
    (extra : Finset (p.TableBin (PackingCounts.subclass e))) (K : ℕ)
    (hbad : (Coverage.badAnchorsAt p (PackingCounts.subclass e) (PackingCounts.label e) v).card ≤ 3 * K)
    (horder : ∀ t ∈ Coverage.edgeTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v,
      rowBaseline e (p.itemAtRole (PackingCounts.subclass e) t .x) ≤
        keyBaseline e (p.itemAtRole (PackingCounts.subclass e) t .anchor))
    (hextra : extra ⊆ Coverage.edgeTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v)
    (hextraRows : ∀ t ∈ extra, rowBaseline e (p.itemAtRole (PackingCounts.subclass e) t .x) ≤ a)
    (hextraDis : Disjoint
      (Coverage.edgePrefixAt p (PackingCounts.subclass e) (PackingCounts.label e) v
        (keyBaseline e) a) extra) :
    (Coverage.baselinePrefixAt p (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) a).card + extra.card ≤ (originalBaselinePrefix D v a).card + 3 * K := by
  apply Coverage.displaced_baseline_prefix_le p (PackingCounts.subclass e) (PackingCounts.label e) v
    (rowBaseline e) (keyBaseline e) a extra (originalBaselinePrefix D v a).card
    (jobPrefix D v a).card K hbad horder hextra hextraRows hextraDis
  · exact jobRowPrefix_card e v a
  · exact keyPrefix_card e v a
  · rw [treeRowPrefix_card, originalBaselinePrefix_card]

private theorem exists_job_of_subclass_s (D : InventoryData) (i : D.Item)
    (h : D.itemSubclass i = .s) :
    ∃ v : D.Vertex, ∃ short : Bool, ∃ j : D.JobCopy v,
      i = ⟨.x, ⟨v, .inr (short, j)⟩⟩ := by
  have hr : i.1 = .x := by
    change D.itemRole i = .x
    rw [← D.itemSubclass_role, h]
    rfl
  rcases i with ⟨role, copy⟩
  dsimp at hr
  subst role
  rcases copy with ⟨v, tree | ⟨short, job⟩⟩
  · exact False.elim (treeSubclass_ne_s tree h)
  · exact ⟨v, short, job, rfl⟩

theorem row_before_current_le_interior (e : D.Item ≃ I.Item) (i : I.Item)
    (hcls : PackingCounts.subclass e i = .s) {v : D.Vertex}
    (r : D.IncidencePosition v)
    (hearlier : rowBaseline e i <
      Geometry.baseline D.graph.edges.length D.R (positionOf D r)) :
    rowBaseline e i ≤
      Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L (positionOf D r) := by
  obtain ⟨w, short, j, hj⟩ := exists_job_of_subclass_s D (e.symm i) hcls
  have hbase : rowBaseline e i =
      Geometry.baseline D.graph.edges.length D.R (D.jobPosition j) := by
    change itemRowBaseline D (e.symm i) = _
    rw [hj]
    rfl
  rw [hbase] at hearlier ⊢
  exact (Geometry.baseline_le_jobInterior D.geometryBound D.L).mpr
    (Geometry.baseline_lt_iff.mp hearlier)

theorem actual_displaced_job_prefix_le
    (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex)
    (r : D.IncidencePosition v) (K : ℕ)
    (hbad : (Coverage.badAnchorsAt p (PackingCounts.subclass e) (PackingCounts.label e) v).card ≤ 3 * K)
    (horder : ∀ t ∈ Coverage.edgeTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v,
      rowBaseline e (p.itemAtRole (PackingCounts.subclass e) t .x) ≤
        keyBaseline e (p.itemAtRole (PackingCounts.subclass e) t .anchor)) :
    (Coverage.baselinePrefixAt p (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e)
      (Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L (positionOf D r))).card +
    (Coverage.displacedTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) (keyBaseline e)
      (Geometry.baseline D.graph.edges.length D.R (positionOf D r))).card ≤
    (originalBaselinePrefix D v
      (Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L (positionOf D r))).card +
      3 * K := by
  classical
  apply actual_displaced_baseline_prefix_le p e v _ _ K hbad horder
  · intro t ht
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
  · intro t ht
    obtain ⟨ht, hbefore⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht, _⟩ := Finset.mem_filter.mp ht
    have hpat := ((Coverage.mem_edgeTuplesAt p (PackingCounts.subclass e)
      (PackingCounts.label e) v t).mp ht).2.2
    apply row_before_current_le_interior e _ _ r hbefore
    rw [p.itemAtRole_subclass (PackingCounts.subclass e) t .x, hpat]
    rfl
  · apply Finset.disjoint_left.mpr
    intro t hearly hcurrent
    have hle := (Finset.mem_filter.mp hearly).2
    have heq := (Finset.mem_filter.mp (Finset.mem_filter.mp hcurrent).1).2
    rw [heq] at hle
    have hcut := (Geometry.jobInterior_mem_jobTestInterval D.graph.edges.length D.R
      D.geometryBound D.L (positionOf D r)).2
    exact (not_lt_of_ge hle) hcut

theorem actual_deadline_deficit_bound
    (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex) (a : ℚ) (K : ℕ)
    (finish : p.TableBin (PackingCounts.subclass e) → ℚ)
    (hbad : (Coverage.badAnchorsAt p (PackingCounts.subclass e) (PackingCounts.label e) v).card ≤ 3 * K)
    (horder : ∀ t ∈ Coverage.edgeTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v,
      rowBaseline e (p.itemAtRole (PackingCounts.subclass e) t .x) ≤
        keyBaseline e (p.itemAtRole (PackingCounts.subclass e) t .anchor))
    (hle : ∀ t ∈ Coverage.mainTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v,
      finish t ≤ rowBaseline e (p.itemAtRole (PackingCounts.subclass e) t .x))
    (hfeasible : ∀ t ∈ Coverage.mainTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v,
      finish t ≤ anchorDeadline e (p.itemAtRole (PackingCounts.subclass e) t .anchor)) :
    (Finset.univ.filter fun z : D.MBase v => D.deadline z ≤ a).card ≤
      (originalBaselinePrefix D v a).card +
      (Coverage.coveringTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v
        (rowBaseline e) finish a).card + 6 * K := by
  classical
  have hbase := actual_displaced_baseline_prefix_le p e v a ∅ K hbad horder
    (Finset.empty_subset _) (by simp) (by simp)
  simp only [Finset.card_empty, Nat.add_zero] at hbase
  have hdeadline := Coverage.deadline_prefix_le_completion_add_loss p
    (PackingCounts.subclass e) (PackingCounts.label e) v (anchorDeadline e) finish a K
    hbad hfeasible
  rw [deadlinePrefix_card] at hdeadline
  have hsplit := Coverage.completion_prefix_decomposition p (PackingCounts.subclass e)
    (PackingCounts.label e) v (rowBaseline e) finish hle a
  omega

theorem actual_current_long_matches_from_correction
    (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex)
    (r : D.IncidencePosition v) (K xplus : ℕ)
    (hbad : (Coverage.badAnchorsAt p (PackingCounts.subclass e) (PackingCounts.label e) v).card ≤ 3 * K)
    (horder : ∀ t ∈ Coverage.edgeTuplesAt p (PackingCounts.subclass e) (PackingCounts.label e) v,
      rowBaseline e (p.itemAtRole (PackingCounts.subclass e) t .x) ≤
        keyBaseline e (p.itemAtRole (PackingCounts.subclass e) t .anchor))
    (hcorrection : D.d + (Coverage.displacedTuplesAt p (PackingCounts.subclass e)
        (PackingCounts.label e) v (rowBaseline e) (keyBaseline e)
        (Geometry.baseline D.graph.edges.length D.R (positionOf D r))).card ≤
      xplus + (Coverage.currentShortMainAt p (PackingCounts.subclass e)
        (PackingCounts.label e) v (rowBaseline e) (rowShort e)
        (Geometry.baseline D.graph.edges.length D.R (positionOf D r))).card + 6 * K) :
    D.d ≤ (Coverage.currentLongEdgeAt p (PackingCounts.subclass e) (PackingCounts.label e) v
      (rowBaseline e) (keyBaseline e) (rowShort e)
      (Geometry.baseline D.graph.edges.length D.R (positionOf D r))).card + xplus + 9 * K := by
  apply Coverage.current_long_matches_from_correction p (PackingCounts.subclass e)
    (PackingCounts.label e) v (rowBaseline e) (keyBaseline e) (rowShort e)
    (Geometry.baseline D.graph.edges.length D.R (positionOf D r)) D.d K xplus
    hbad horder (rowShort_implies_job e) _ _ hcorrection
  · rw [currentKeyItems_card, jobsAt_position_card]
  · rw [currentShortItems_card, jobsAt_position_card]

end InventoryCoverage
end BinPackingGap

end

end OAI
