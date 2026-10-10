import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import OAI.Computability.BinPacking.Inventory.InventoryPrefixConservation
import OAI.Computability.BinPacking.Packing.PackingFeasibility

namespace OAI

noncomputable section

namespace BinPackingGap
namespace InventoryData

section

variable (D : InventoryData) {b : ℕ}

def earlierKeyItems (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    Finset D.packingInstance.Item := (D.earlierKeys h hle).image D.itemEquiv

def earlierWItems (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    Finset D.packingInstance.Item := (D.earlierW h hle).image D.itemEquiv

theorem earlierKeyItems_card (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    (D.earlierKeyItems h hle).card = 2 * D.d * D.R * h := by
  rw [earlierKeyItems, Finset.card_image_of_injective _ D.itemEquiv.injective,
    D.earlierKeys_card]

theorem earlierWItems_card (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    (D.earlierWItems h hle).card = 2 * D.d * D.R * h := by
  rw [earlierWItems, Finset.card_image_of_injective _ D.itemEquiv.injective,
    D.earlierW_card]

theorem mem_earlierKeyItems (h : ℕ) (hle : h ≤ D.graph.edges.length)
    (i : D.packingInstance.Item) :
    i ∈ D.earlierKeyItems h hle ↔
      ∃ j : Σ v : D.Vertex, D.JobCopy v,
        D.itemEquiv (D.keyItem j) = i ∧ (D.jobPosition j.2).1.val < h := by
  classical
  constructor
  · intro hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨j, rfl, hj⟩ := (D.mem_earlierKeys h hle a).mp ha
    exact ⟨j, rfl, hj⟩
  · rintro ⟨j, rfl, hj⟩
    exact Finset.mem_image.mpr ⟨D.keyItem j,
      (D.mem_earlierKeys h hle _).mpr ⟨j, rfl, hj⟩, rfl⟩

theorem mem_earlierWItems (h : ℕ) (hle : h ≤ D.graph.edges.length)
    (i : D.packingInstance.Item) :
    i ∈ D.earlierWItems h hle ↔
      ∃ w : (D.Edge × Bool) × Fin (D.d * D.R),
        D.itemEquiv (D.edgeResourceItem w) = i ∧ w.1.1.val < h := by
  classical
  constructor
  · intro hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨w, rfl, hw⟩ := (D.mem_earlierW h hle a).mp ha
    exact ⟨w, rfl, hw⟩
  · rintro ⟨w, rfl, hw⟩
    exact Finset.mem_image.mpr ⟨D.edgeResourceItem w,
      (D.mem_earlierW h hle _).mpr ⟨w, rfl, hw⟩, rfl⟩

@[simp] theorem keyItem_mem_earlierKeyItems (h : ℕ) (hle : h ≤ D.graph.edges.length)
    (j : Σ v : D.Vertex, D.JobCopy v) :
    D.itemEquiv (D.keyItem j) ∈ D.earlierKeyItems h hle ↔
      (D.jobPosition j.2).1.val < h := by
  rw [D.mem_earlierKeyItems]
  constructor
  · rintro ⟨z, hz, hlt⟩
    have heq := D.keyItem_injective (D.itemEquiv.injective hz)
    subst z
    exact hlt
  · intro hlt
    exact ⟨j, rfl, hlt⟩

@[simp] theorem edgeResourceItem_mem_earlierWItems
    (h : ℕ) (hle : h ≤ D.graph.edges.length)
    (w : (D.Edge × Bool) × Fin (D.d * D.R)) :
    D.itemEquiv (D.edgeResourceItem w) ∈ D.earlierWItems h hle ↔ w.1.1.val < h := by
  rw [D.mem_earlierWItems]
  constructor
  · rintro ⟨z, hz, hlt⟩
    have heq := D.edgeResourceItem_injective (D.itemEquiv.injective hz)
    simpa only [heq] using hlt
  · intro hlt
    exact ⟨w, rfl, hlt⟩

def earlierGoodKeyTuples (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) : Finset (p.TableBin D.encodedSubclass) := by
  classical
  exact Finset.univ.filter fun t => p.IsGoodTableBin D.encodedSubclass D.encodedLabel t ∧
    p.itemAtRole D.encodedSubclass t .anchor ∈ D.earlierKeyItems h hle

@[simp] theorem mem_earlierGoodKeyTuples (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) (t : p.TableBin D.encodedSubclass) :
    t ∈ D.earlierGoodKeyTuples p h hle ↔
      p.IsGoodTableBin D.encodedSubclass D.encodedLabel t ∧
        p.itemAtRole D.encodedSubclass t .anchor ∈ D.earlierKeyItems h hle := by
  classical
  simp [earlierGoodKeyTuples]

theorem earlierGoodKeyTuples_anchor_subset (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    Coverage.roleItems p D.encodedSubclass (D.earlierGoodKeyTuples p h hle) .anchor ⊆
      D.earlierKeyItems h hle := by
  intro i hi
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
  exact ((D.mem_earlierGoodKeyTuples p h hle t).mp ht).2

theorem earlierGoodKeyTuples_edge (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) (t : p.TableBin D.encodedSubclass)
    (ht : t ∈ D.earlierGoodKeyTuples p h hle) :
    ∃ v, t ∈ Coverage.edgeTuplesAt p D.encodedSubclass D.encodedLabel v := by
  obtain ⟨hgood, hkey⟩ := (D.mem_earlierGoodKeyTuples p h hle t).mp ht
  obtain ⟨j, hj, _⟩ := (D.mem_earlierKeyItems h hle _).mp hkey
  have hlabel : D.encodedLabel (p.itemAtRole D.encodedSubclass t .anchor) = some j.1 := by
    rw [← hj]
    simp [encodedLabel]
  have hsub : D.encodedSubclass (p.itemAtRole D.encodedSubclass t .anchor) = .y := by
    rw [← hj]
    simp [encodedSubclass]
  have hpat : p.tablePattern D.encodedSubclass t = .edgeJob := by
    have hx := (p.itemAtRole_subclass D.encodedSubclass t .anchor).symm.trans hsub
    cases hp : p.tablePattern D.encodedSubclass t <;> simp_all [patternSubclass]
  exact ⟨j.1, (Coverage.mem_edgeTuplesAt p D.encodedSubclass D.encodedLabel j.1 t).mpr
    ⟨hgood, hlabel, hpat⟩⟩

theorem earlierGoodKeyTuples_global_subset (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    Coverage.roleItems p D.encodedSubclass (D.earlierGoodKeyTuples p h hle) .«global» ⊆
      D.earlierWItems h hle := by
  classical
  intro i hi
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨v, htv⟩ := D.earlierGoodKeyTuples_edge p h hle t ht
  obtain ⟨w, _, _, he⟩ := PackingCounts.edge_tuple_feasible p D.itemEquiv
    D.packingInstance_size_eq v t htv
  obtain ⟨j, hj, hjlt⟩ := (D.mem_earlierKeyItems h hle _).mp
    (((D.mem_earlierGoodKeyTuples p h hle t).mp ht).2)
  have hkey : D.itemEquiv (D.keyItem ⟨(PackingCounts.anchorCopy p D.itemEquiv t).1, w.key⟩) =
      p.itemAtRole D.encodedSubclass t .anchor := by
    have ha := congrArg
      (fun a : D.AnchorAt (PackingCounts.anchorCopy p D.itemEquiv t).1 =>
        D.itemEquiv (⟨.anchor,
          ⟨(PackingCounts.anchorCopy p D.itemEquiv t).1, a⟩⟩ : D.Item)) w.anchor_eq
    have heta := congrArg
      (fun a : Σ v : D.Vertex, D.AnchorAt v => D.itemEquiv (⟨.anchor, a⟩ : D.Item))
      (Sigma.eta (PackingCounts.anchorCopy p D.itemEquiv t))
    exact ha.symm.trans (heta.trans (PackingCounts.roleCopy_item p D.itemEquiv t .anchor))
  have hjEq := D.keyItem_injective (D.itemEquiv.injective (hkey.trans hj.symm))
  have hpos := congrArg (fun z : Σ v : D.Vertex, D.JobCopy v =>
    (D.jobPosition z.2).1.val) hjEq
  have hwe : w.edge.val < h := lt_of_le_of_lt he (by simpa only [hpos] using hjlt)
  apply (D.mem_earlierWItems h hle _).mpr
  refine ⟨((w.edge, w.permit), w.globalIndex), ?_, hwe⟩
  exact (congrArg (fun g : D.GlobalCopy => D.itemEquiv (⟨.«global», g⟩ : D.Item))
    w.global_eq.symm).trans (PackingCounts.roleCopy_item p D.itemEquiv t .«global»)

def remainingEarlierW (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) : Finset D.packingInstance.Item :=
  D.earlierWItems h hle \
    Coverage.roleItems p D.encodedSubclass (D.earlierGoodKeyTuples p h hle) .«global»

theorem remainingEarlierW_card_eq_missingKeys (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    (D.remainingEarlierW p h hle).card =
      (D.earlierKeyItems h hle \
        Coverage.roleItems p D.encodedSubclass (D.earlierGoodKeyTuples p h hle) .anchor).card := by
  rw [remainingEarlierW, Finset.card_sdiff_of_subset (D.earlierGoodKeyTuples_global_subset p h hle),
    Finset.card_sdiff_of_subset (D.earlierGoodKeyTuples_anchor_subset p h hle),
    Coverage.roleItems_card, Coverage.roleItems_card, D.earlierWItems_card,
    D.earlierKeyItems_card]

theorem missingEarlierKeys_subset_bad (p : Packing D.packingInstance b)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    D.earlierKeyItems h hle \
      Coverage.roleItems p D.encodedSubclass (D.earlierGoodKeyTuples p h hle) .anchor ⊆
        (Finset.univ : Finset D.Vertex).biUnion
          (Coverage.badAnchorsAt p D.encodedSubclass D.encodedLabel) := by
  classical
  intro i hi
  obtain ⟨hik, hin⟩ := Finset.mem_sdiff.mp hi
  obtain ⟨j, hj, _⟩ := (D.mem_earlierKeyItems h hle i).mp hik
  apply Finset.mem_biUnion.mpr
  refine ⟨j.1, Finset.mem_univ _, ?_⟩
  apply (Coverage.mem_badAnchorsAt p D.encodedSubclass D.encodedLabel j.1 i).mpr
  constructor
  · apply (Coverage.mem_anchorItemsAt D.encodedSubclass D.encodedLabel j.1 i).mpr
    rw [← hj]
    simp [encodedSubclass, encodedLabel, Subclass.role]
  · intro hgood
    obtain ⟨t, ht, hti⟩ := Finset.mem_image.mp hgood
    apply hin
    refine Finset.mem_image.mpr ⟨t, ?_, hti⟩
    apply (D.mem_earlierGoodKeyTuples p h hle t).mpr
    refine ⟨((Coverage.mem_goodTuplesAt p D.encodedSubclass D.encodedLabel j.1 t).mp ht).1, ?_⟩
    simpa only [hti] using hik

theorem remainingEarlierW_card_le {c : ℕ} (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c)
    (h : ℕ) (hle : h ≤ D.graph.edges.length) :
    (D.remainingEarlierW p h hle).card ≤ 3 * D.graph.n * lossAllowance c := by
  rw [D.remainingEarlierW_card_eq_missingKeys]
  exact (Finset.card_le_card (D.missingEarlierKeys_subset_bad p h hle)).trans
    (D.badAnchors_global_card_le hk p hb)

end

open scoped BigOperators
open PackingCounts

variable (D : InventoryData) {b : ℕ}

def edgeLongTuplesAt (p : Packing D.packingInstance b) (edge : D.Edge)
    (q : Fin 2 × Fin D.R) : Finset (p.TableBin D.encodedSubclass) :=
  Coverage.currentLongEdgeAt p D.encodedSubclass D.encodedLabel
    (D.graph.endpoint edge q.1)
    (InventoryCoverage.rowBaseline D.itemEquiv)
    (InventoryCoverage.keyBaseline D.itemEquiv)
    (InventoryCoverage.rowShort D.itemEquiv)
    (Geometry.baseline D.graph.edges.length D.R (edge, q.2))

@[simp] theorem mem_edgeLongTuplesAt (p : Packing D.packingInstance b) (edge : D.Edge)
    (q : Fin 2 × Fin D.R) (t : p.TableBin D.encodedSubclass) :
    t ∈ D.edgeLongTuplesAt p edge q ↔
      t ∈ Coverage.edgeTuplesAt p D.encodedSubclass D.encodedLabel
        (D.graph.endpoint edge q.1) ∧
      InventoryCoverage.keyBaseline D.itemEquiv
        (p.itemAtRole D.encodedSubclass t .anchor) =
          Geometry.baseline D.graph.edges.length D.R (edge, q.2) ∧
      InventoryCoverage.rowBaseline D.itemEquiv
        (p.itemAtRole D.encodedSubclass t .x) =
          Geometry.baseline D.graph.edges.length D.R (edge, q.2) ∧
      InventoryCoverage.rowShort D.itemEquiv
        (p.itemAtRole D.encodedSubclass t .x) ≠ true := by
  classical
  simp [edgeLongTuplesAt, Coverage.currentLongEdgeAt, Coverage.currentEdgeTuplesAt,
    and_assoc]

theorem edgeLongTuplesAt_disjoint (p : Packing D.packingInstance b) (edge : D.Edge)
    {q r : Fin 2 × Fin D.R} (hne : q ≠ r) :
    Disjoint (D.edgeLongTuplesAt p edge q) (D.edgeLongTuplesAt p edge r) := by
  classical
  apply Finset.disjoint_left.mpr
  intro t hq hr
  obtain ⟨hGq, hkeyq, _, _⟩ := (D.mem_edgeLongTuplesAt p edge q t).mp hq
  obtain ⟨hGr, hkeyr, _, _⟩ := (D.mem_edgeLongTuplesAt p edge r t).mp hr
  have hlq := ((Coverage.mem_edgeTuplesAt p D.encodedSubclass D.encodedLabel
    (D.graph.endpoint edge q.1) t).mp hGq).2.1
  have hlr := ((Coverage.mem_edgeTuplesAt p D.encodedSubclass D.encodedLabel
    (D.graph.endpoint edge r.1) t).mp hGr).2.1
  have hside : q.1 = r.1 := D.graph.endpoint_injective edge
    (Option.some.inj (hlq.symm.trans hlr))
  have hrep : q.2 = r.2 := congrArg (fun z : D.Edge × Fin D.R => z.2)
    ((Geometry.baseline_eq_iff (r := (edge, q.2)) (s := (edge, r.2))).mp
      (hkeyq.symm.trans hkeyr))
  exact hne (Prod.ext hside hrep)

def edgeLongTuples (p : Packing D.packingInstance b) (edge : D.Edge)
    (J : Finset (Fin D.R)) : Finset (p.TableBin D.encodedSubclass) := by
  classical
  exact ((Finset.univ : Finset (Fin 2)).product J).biUnion (D.edgeLongTuplesAt p edge)

theorem edgeLongTuples_card (p : Packing D.packingInstance b) (edge : D.Edge)
    (J : Finset (Fin D.R)) :
    (D.edgeLongTuples p edge J).card =
      ∑ side : Fin 2, ∑ rep ∈ J, (D.edgeLongTuplesAt p edge (side, rep)).card := by
  classical
  have hdis : ∀ q ∈ (Finset.univ : Finset (Fin 2)).product J,
      ∀ r ∈ (Finset.univ : Finset (Fin 2)).product J,
        q ≠ r → Disjoint (D.edgeLongTuplesAt p edge q) (D.edgeLongTuplesAt p edge r) := by
    intro q _ r _ hne
    exact D.edgeLongTuplesAt_disjoint p edge hne
  rw [edgeLongTuples, Finset.card_biUnion hdis]
  exact Finset.sum_product (Finset.univ : Finset (Fin 2)) J
    (fun q : Fin 2 × Fin D.R => (D.edgeLongTuplesAt p edge q).card)

theorem edgeLongTuplesAt_witness (p : Packing D.packingInstance b) (edge : D.Edge)
    (q : Fin 2 × Fin D.R) (t : p.TableBin D.encodedSubclass)
    (ht : t ∈ D.edgeLongTuplesAt p edge q) :
    ∃ w : EdgeTupleData p D.itemEquiv t, w.expression ≤ 0 ∧
      D.jobPosition w.key = (edge, q.2) ∧
      D.jobPosition w.row = (edge, q.2) ∧ w.short = false := by
  obtain ⟨hG, hkey, hrow, hshort⟩ := (D.mem_edgeLongTuplesAt p edge q t).mp ht
  obtain ⟨w, hf, _, _⟩ := edge_tuple_feasible p D.itemEquiv
    D.packingInstance_size_eq (D.graph.endpoint edge q.1) t hG
  have hcopy : anchorCopy p D.itemEquiv t =
      ⟨(anchorCopy p D.itemEquiv t).1, .inr w.key⟩ := by
    conv_lhs => rw [← Sigma.eta (anchorCopy p D.itemEquiv t)]
    rw [w.anchor_eq]
  erw [InventoryCoverage.keyBaseline_selected_of_key p D.itemEquiv t _ w.key hcopy] at hkey
  erw [InventoryCoverage.rowBaseline_selected p D.itemEquiv t, w.row_eq] at hrow
  change Geometry.baseline D.graph.edges.length D.R (D.jobPosition w.row) = _ at hrow
  erw [InventoryCoverage.rowShort_selected p D.itemEquiv t, w.row_eq] at hshort
  change w.short ≠ true at hshort
  refine ⟨w, hf, Geometry.baseline_eq_iff.mp hkey, Geometry.baseline_eq_iff.mp hrow, ?_⟩
  exact Bool.eq_false_of_not_eq_true hshort

private theorem witness_key_item (p : Packing D.packingInstance b)
    (t : p.TableBin D.encodedSubclass) (w : EdgeTupleData p D.itemEquiv t) :
    D.itemEquiv (D.keyItem ⟨(anchorCopy p D.itemEquiv t).1, w.key⟩) =
      p.itemAtRole D.encodedSubclass t .anchor := by
  erw [← roleCopy_item p D.itemEquiv t .anchor]
  apply congrArg D.itemEquiv
  change (⟨.anchor, ⟨_, .inr w.key⟩⟩ : D.Item) =
    ⟨.anchor, anchorCopy p D.itemEquiv t⟩
  conv_rhs => rw [← Sigma.eta (anchorCopy p D.itemEquiv t), w.anchor_eq]

private theorem witness_global_item (p : Packing D.packingInstance b)
    (t : p.TableBin D.encodedSubclass) (w : EdgeTupleData p D.itemEquiv t) :
    D.itemEquiv (D.edgeResourceItem ((w.edge, w.permit), w.globalIndex)) =
      p.itemAtRole D.encodedSubclass t .«global» := by
  erw [← roleCopy_item p D.itemEquiv t .«global»]
  change D.itemEquiv ⟨.«global», ⟨.edge w.edge w.permit, w.globalIndex⟩⟩ =
    D.itemEquiv ⟨.«global», globalCopy p D.itemEquiv t⟩
  rw [w.global_eq]

theorem edgeLongTuplesAt_not_earlierGoodKeyTuples (p : Packing D.packingInstance b)
    (edge : D.Edge) (q : Fin 2 × Fin D.R) (t : p.TableBin D.encodedSubclass)
    (ht : t ∈ D.edgeLongTuplesAt p edge q) :
    t ∉ D.earlierGoodKeyTuples p edge.val edge.isLt.le := by
  obtain ⟨w, _, hkey, _, _⟩ := D.edgeLongTuplesAt_witness p edge q t ht
  intro hearlier
  have hmem := ((D.mem_earlierGoodKeyTuples p edge.val edge.isLt.le t).mp hearlier).2
  rw [← D.witness_key_item p t w, D.keyItem_mem_earlierKeyItems] at hmem
  simp only [hkey, Nat.lt_irrefl] at hmem

theorem edgeLongTuplesAt_global_not_used_earlier (p : Packing D.packingInstance b)
    (edge : D.Edge) (q : Fin 2 × Fin D.R) (t : p.TableBin D.encodedSubclass)
    (ht : t ∈ D.edgeLongTuplesAt p edge q) :
    p.itemAtRole D.encodedSubclass t .«global» ∉
      Coverage.roleItems p D.encodedSubclass
        (D.earlierGoodKeyTuples p edge.val edge.isLt.le) .«global» := by
  intro hi
  obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hi
  have hut : u = t := p.itemAtRole_injective D.encodedSubclass .«global» heq
  subst u
  exact D.edgeLongTuplesAt_not_earlierGoodKeyTuples p edge q t ht hu

theorem edgeLongTuplesAt_global_mem (p : Packing D.packingInstance b)
    (edge : D.Edge) (q : Fin 2 × Fin D.R) (t : p.TableBin D.encodedSubclass)
    (ht : t ∈ D.edgeLongTuplesAt p edge q) :
    p.itemAtRole D.encodedSubclass t .«global» ∈
      globalResources D.itemEquiv (.edge edge true) ∪
        D.remainingEarlierW p edge.val edge.isLt.le := by
  classical
  obtain ⟨w, hf, hkey, hrow, hshort⟩ := D.edgeLongTuplesAt_witness p edge q t ht
  have hresource := w.exact_long_resource hf (hrow.trans hkey.symm) hshort
  rcases hresource with hearlier | ⟨heq, hpermit⟩
  · apply Finset.mem_union_right
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, D.edgeLongTuplesAt_global_not_used_earlier p edge q t ht⟩
    apply (D.mem_earlierWItems edge.val edge.isLt.le _).mpr
    refine ⟨((w.edge, w.permit), w.globalIndex), D.witness_global_item p t w, ?_⟩
    have hlt : w.edge < edge := by simpa only [hkey] using hearlier
    exact hlt
  · apply Finset.mem_union_left
    apply (selected_global_resource_iff p D.itemEquiv t (.edge edge true)).mpr
    rw [w.global_eq]
    have hedge : w.edge = edge := by simpa only [hkey] using heq
    simp only [hedge, hpermit]

theorem edgeLongTuples_global_subset (p : Packing D.packingInstance b)
    (edge : D.Edge) (J : Finset (Fin D.R)) :
    Coverage.roleItems p D.encodedSubclass (D.edgeLongTuples p edge J) .«global» ⊆
      globalResources D.itemEquiv (.edge edge true) ∪
        D.remainingEarlierW p edge.val edge.isLt.le := by
  classical
  intro i hi
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨q, _, hq⟩ := Finset.mem_biUnion.mp ht
  exact D.edgeLongTuplesAt_global_mem p edge q t hq

theorem edge_long_matches_capacity {c : ℕ} (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c)
    (edge : D.Edge) (J : Finset (Fin D.R)) :
    (∑ side : Fin 2, ∑ rep ∈ J, (D.edgeLongTuplesAt p edge (side, rep)).card) ≤
      D.d * D.R + 3 * D.graph.n * lossAllowance c := by
  classical
  rw [← D.edgeLongTuples_card]
  have hbound := Finset.card_le_card (D.edgeLongTuples_global_subset p edge J)
  rw [Coverage.roleItems_card] at hbound
  refine hbound.trans ((Finset.card_union_le _ _).trans ?_)
  rw [globalResources_card]
  change D.d * D.R + (D.remainingEarlierW p edge.val edge.isLt.le).card ≤ _
  exact Nat.add_le_add_left (D.remainingEarlierW_card_le hk p hb edge.val edge.isLt.le) _

theorem edge_long_matches_capacity_raw {c : ℕ} (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c)
    (edge : D.Edge) (J : Finset (Fin D.R)) :
    (∑ side : Fin 2, ∑ rep ∈ J,
      (Coverage.currentLongEdgeAt p D.encodedSubclass D.encodedLabel
        (D.graph.endpoint edge side)
        (InventoryCoverage.rowBaseline D.itemEquiv)
        (InventoryCoverage.keyBaseline D.itemEquiv)
        (InventoryCoverage.rowShort D.itemEquiv)
        (Geometry.baseline D.graph.edges.length D.R (edge, rep))).card) ≤
      D.d * D.R + 3 * D.graph.n * lossAllowance c :=
  D.edge_long_matches_capacity hk p hb edge J

end InventoryData
end BinPackingGap

end

end OAI
