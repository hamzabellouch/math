import Mathlib.Basic.Real.Basic
import Mathlib.Logic.Embedding.Basic
import OAI.Computability.BinPacking.Packing.GoodAnchorBound
import OAI.Computability.BinPacking.Packing.PackingCoordinates

namespace OAI

noncomputable section

namespace BinPackingGap

section

open scoped BigOperators

namespace InventoryData

variable (D : InventoryData)

def itemSize (i : D.Item) : ℚ :=
  encodedSize (D.itemSubclass i) (D.itemLabel i) (D.itemCoordinate i)

theorem itemSize_mem_interval (i : D.Item) :
    1 / 6 < D.itemSize i ∧ D.itemSize i < 1 :=
  encodedSize_mem_interval _ _ _ (D.itemCoordinate_abs_le_six i)

theorem itemSize_pos (i : D.Item) : 0 < D.itemSize i :=
  lt_trans (by norm_num) (D.itemSize_mem_interval i).1

theorem itemSize_le_one (i : D.Item) : D.itemSize i ≤ 1 :=
  (D.itemSize_mem_interval i).2.le

def packingInstance : Instance :=
  Instance.ofFintype D.itemSize D.itemSize_pos D.itemSize_le_one

def itemEquiv : D.Item ≃ D.packingInstance.Item := Fintype.equivFin D.Item

def encodedSubclass (i : D.packingInstance.Item) : Subclass :=
  D.itemSubclass (D.itemEquiv.symm i)

def encodedLabel (i : D.packingInstance.Item) : Option D.Vertex :=
  D.itemLabel (D.itemEquiv.symm i)

def encodedCoordinate (i : D.packingInstance.Item) : ℚ :=
  D.itemCoordinate (D.itemEquiv.symm i)

theorem packingInstance_size_eq (i : D.packingInstance.Item) :
    D.packingInstance.size i =
      encodedSize (D.encodedSubclass i) (D.encodedLabel i) (D.encodedCoordinate i) := rfl

theorem encodedCoordinate_abs_le_six (i : D.packingInstance.Item) :
    |D.encodedCoordinate i| ≤ 6 := D.itemCoordinate_abs_le_six _

theorem packingInstance_size_mem_interval (i : D.packingInstance.Item) :
    1 / 6 < D.packingInstance.size i ∧ D.packingInstance.size i < 1 :=
  D.itemSize_mem_interval _

theorem packingInstance_n (hk : D.k ≤ D.graph.n) :
    D.packingInstance.n = 5 * D.B := D.card_item hk

theorem encoded_primaryScore_sum_eq_zero (hk : D.k ≤ D.graph.n) :
    (∑ i : D.packingInstance.Item, primaryScore (D.encodedSubclass i)) = 0 := by
  change (∑ i, primaryScore (D.itemSubclass (D.itemEquiv.symm i))) = 0
  rw [D.itemEquiv.symm.sum_comp (fun i : D.Item => primaryScore (D.itemSubclass i))]
  exact D.total_primaryScore_eq_zero hk

theorem encoded_secondaryScore_sum_eq_zero :
    (∑ i : D.packingInstance.Item,
      secondaryScore (D.encodedSubclass i) (D.encodedLabel i)) = 0 := by
  change (∑ i, secondaryScore (D.itemSubclass (D.itemEquiv.symm i))
    (D.itemLabel (D.itemEquiv.symm i))) = 0
  rw [D.itemEquiv.symm.sum_comp
    (fun i : D.Item => secondaryScore (D.itemSubclass i) (D.itemLabel i))]
  exact D.total_secondaryScore_eq_zero

theorem encoded_labelledRoleCount (r : Role) (v : D.Vertex) :
    labelledRoleCount D.encodedSubclass D.encodedLabel r v =
      labelledRoleCount D.itemSubclass D.itemLabel r v := by
  unfold labelledRoleCount encodedSubclass encodedLabel
  exact D.itemEquiv.symm.sum_comp
    (fun i : D.Item => if (D.itemSubclass i).role = r ∧ D.itemLabel i = some v
      then (1 : ℤ) else 0)

theorem encoded_labelledRoleCount_x (v : D.Vertex) :
    labelledRoleCount D.encodedSubclass D.encodedLabel .x v =
      ((D.t + 2 * D.J v : ℕ) : ℤ) := by
  rw [D.encoded_labelledRoleCount, D.labelledRoleCount_x]

theorem encoded_labelledRoleCount_anchor (v : D.Vertex) :
    labelledRoleCount D.encodedSubclass D.encodedLabel .anchor v =
      ((D.t + 2 * D.J v : ℕ) : ℤ) := by
  rw [D.encoded_labelledRoleCount, D.labelledRoleCount_anchor]

theorem encoded_labelledRoleCount_local (v : D.Vertex) :
    labelledRoleCount D.encodedSubclass D.encodedLabel .«local» v =
      ((D.t + 2 * D.J v : ℕ) : ℤ) := by
  rw [D.encoded_labelledRoleCount, D.labelledRoleCount_local]

theorem itemLabel_some_of_labelled (i : D.Item)
    (h : D.itemRole i = .x ∨ D.itemRole i = .anchor ∨ D.itemRole i = .«local») :
    ∃ v, D.itemLabel i = some v := by
  rcases i with ⟨r, i⟩
  cases r <;> simp only [itemRole] at h
  · exact ⟨i.1, rfl⟩
  · exact ⟨i.1, rfl⟩
  · simp at h
  · exact ⟨i.1, rfl⟩
  · simp at h

theorem itemLabel_none_of_unlabelled (i : D.Item)
    (h : D.itemRole i = .«global» ∨ D.itemRole i = .flag) :
    D.itemLabel i = none := by
  rcases i with ⟨r, i⟩
  cases r <;> simp_all [itemRole, itemLabel]

theorem encodedLabel_some_of_labelled (i : D.packingInstance.Item)
    (h : (D.encodedSubclass i).role = .x ∨ (D.encodedSubclass i).role = .anchor ∨
      (D.encodedSubclass i).role = .«local») :
    ∃ v, D.encodedLabel i = some v := by
  apply D.itemLabel_some_of_labelled (D.itemEquiv.symm i)
  simpa only [encodedSubclass, D.itemSubclass_role] using h

theorem encodedLabel_none_of_unlabelled (i : D.packingInstance.Item)
    (h : (D.encodedSubclass i).role = .«global» ∨ (D.encodedSubclass i).role = .flag) :
    D.encodedLabel i = none := by
  apply D.itemLabel_none_of_unlabelled (D.itemEquiv.symm i)
  simpa only [encodedSubclass, D.itemSubclass_role] using h

end InventoryData

end

namespace InventoryData

open scoped BigOperators

variable (D : InventoryData)

def roleLabelData : RoleLabelData D.encodedSubclass D.encodedLabel :=
  RoleLabelData.of_valid D.encodedSubclass D.encodedLabel
    D.encodedLabel_some_of_labelled D.encodedLabel_none_of_unlabelled

theorem roleLabelData_anchor_row_count (v : D.Vertex) :
    (Finset.univ.filter fun i => D.roleLabelData.anchor i = v).card =
      (Finset.univ.filter fun i => D.roleLabelData.row i = v).card := by
  classical
  have h : ((Finset.univ.filter fun i => D.roleLabelData.anchor i = v).card : ℤ) =
      ((Finset.univ.filter fun i => D.roleLabelData.row i = v).card : ℤ) := by
    rw [D.roleLabelData.anchor_count, D.roleLabelData.row_count,
      D.encoded_labelledRoleCount_anchor, D.encoded_labelledRoleCount_x]
  exact_mod_cast h

theorem roleLabelData_anchor_local_count (v : D.Vertex) :
    (Finset.univ.filter fun i => D.roleLabelData.anchor i = v).card =
      (Finset.univ.filter fun i => D.roleLabelData.localLabel i = v).card := by
  classical
  have h : ((Finset.univ.filter fun i => D.roleLabelData.anchor i = v).card : ℤ) =
      ((Finset.univ.filter fun i => D.roleLabelData.localLabel i = v).card : ℤ) := by
    rw [D.roleLabelData.anchor_count, D.roleLabelData.local_count,
      D.encoded_labelledRoleCount_anchor, D.encoded_labelledRoleCount_local]
  exact_mod_cast h

theorem outsideTableItems_card_lt_lossAllowance {b c : ℕ}
    (hk : D.k ≤ D.graph.n) (p : Packing D.packingInstance b) (hb : b ≤ D.B + c) :
    (p.outsideTableItems D.encodedSubclass).card < lossAllowance c := by
  simpa only [lossAllowance, primaryScoreBound, primaryBound] using
    p.outsideTableItems_card_lt D.encodedSubclass D.encodedLabel D.encodedCoordinate
      D.packingInstance_size_eq D.encodedCoordinate_abs_le_six D.B c
      (D.packingInstance_n hk) hb (D.encoded_primaryScore_sum_eq_zero hk)

theorem badAnchorsAt_card_le {b c : ℕ} (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c) (v : D.Vertex) :
    (Coverage.badAnchorsAt p D.encodedSubclass D.encodedLabel v).card ≤
      3 * lossAllowance c := by
  simpa only [lossAllowance, primaryScoreBound, primaryBound] using
    Coverage.badAnchorsAt_card_le p D.encodedSubclass D.encodedLabel D.roleLabelData
      D.encodedCoordinate D.packingInstance_size_eq D.encodedCoordinate_abs_le_six D.B c
      (D.packingInstance_n hk) hb (D.encoded_primaryScore_sum_eq_zero hk)
      D.roleLabelData_anchor_row_count D.roleLabelData_anchor_local_count v

theorem anchor_subset_loss_le {b c : ℕ} (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c) (v : D.Vertex)
    (s : Finset D.packingInstance.Item)
    (hs : s ⊆ Coverage.anchorItemsAt D.encodedSubclass D.encodedLabel v) :
    (s \ Coverage.roleItems p D.encodedSubclass
      (Coverage.goodTuplesAt p D.encodedSubclass D.encodedLabel v) .anchor).card ≤
      3 * lossAllowance c := by
  simpa only [lossAllowance, primaryScoreBound, primaryBound] using
    Coverage.anchor_subset_loss_le p D.encodedSubclass D.encodedLabel D.roleLabelData
      D.encodedCoordinate D.packingInstance_size_eq D.encodedCoordinate_abs_le_six D.B c
      (D.packingInstance_n hk) hb (D.encoded_primaryScore_sum_eq_zero hk)
      D.roleLabelData_anchor_row_count D.roleLabelData_anchor_local_count v s hs

theorem badAnchors_global_card_le {b c : ℕ} (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c) :
    ((Finset.univ : Finset D.Vertex).biUnion
      (Coverage.badAnchorsAt p D.encodedSubclass D.encodedLabel)).card ≤
      3 * D.graph.n * lossAllowance c := by
  simpa only [lossAllowance, primaryScoreBound, primaryBound] using
    Coverage.badAnchors_global_card_le p D.encodedSubclass D.encodedLabel D.roleLabelData
      D.encodedCoordinate D.packingInstance_size_eq D.encodedCoordinate_abs_le_six D.B c
      (D.packingInstance_n hk) hb (D.encoded_primaryScore_sum_eq_zero hk)
      D.roleLabelData_anchor_row_count D.roleLabelData_anchor_local_count

end InventoryData
end BinPackingGap

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

def taggedItem (r : Role) : D.RoleCopies r ↪ D.packingInstance.Item :=
  (Function.Embedding.sigmaMk r).trans D.itemEquiv.toEmbedding

@[simp] theorem taggedItem_apply (r : Role) (c : D.RoleCopies r) :
    D.taggedItem r c = D.itemEquiv ⟨r, c⟩ := rfl

def globalCopyEmbedding (s : GlobalSpecies D.graph) :
    Fin (D.globalStock s) ↪ D.packingInstance.Item :=
  (Function.Embedding.sigmaMk s).trans (D.taggedItem .«global»)

def flagCopyEmbedding (s : FlagSpecies) :
    Fin (D.flagStock s) ↪ D.packingInstance.Item :=
  (Function.Embedding.sigmaMk s).trans (D.taggedItem .flag)

@[simp] theorem globalCopyEmbedding_apply (s : GlobalSpecies D.graph)
    (j : Fin (D.globalStock s)) :
    D.globalCopyEmbedding s j = D.itemEquiv ⟨.«global», ⟨s, j⟩⟩ := rfl

@[simp] theorem flagCopyEmbedding_apply (s : FlagSpecies) (j : Fin (D.flagStock s)) :
    D.flagCopyEmbedding s j = D.itemEquiv ⟨.flag, ⟨s, j⟩⟩ := rfl

def physicalGlobalPool (s : GlobalSpecies D.graph) : Finset D.packingInstance.Item :=
  Finset.univ.map (D.globalCopyEmbedding s)

def physicalFlagPool (s : FlagSpecies) : Finset D.packingInstance.Item :=
  Finset.univ.map (D.flagCopyEmbedding s)

def labeledItems : Finset D.packingInstance.Item :=
  Finset.univ.filter (fun i =>
    (D.itemEquiv.symm i).1 = .x ∨ (D.itemEquiv.symm i).1 = .anchor ∨
      (D.itemEquiv.symm i).1 = .«local»)

@[simp] theorem card_physicalGlobalPool (s : GlobalSpecies D.graph) :
    (D.physicalGlobalPool s).card = D.globalStock s := by
  simp [physicalGlobalPool]

@[simp] theorem card_physicalFlagPool (s : FlagSpecies) :
    (D.physicalFlagPool s).card = D.flagStock s := by
  simp [physicalFlagPool]

theorem physicalGlobalPool_nonempty_iff (s : GlobalSpecies D.graph) :
    (D.physicalGlobalPool s).Nonempty ↔ 0 < D.globalStock s := by
  rw [← Finset.card_pos, card_physicalGlobalPool]

theorem physicalFlagPool_nonempty_iff (s : FlagSpecies) :
    (D.physicalFlagPool s).Nonempty ↔ 0 < D.flagStock s := by
  rw [← Finset.card_pos, card_physicalFlagPool]

theorem mem_physicalGlobalPool (s : GlobalSpecies D.graph) (i : D.packingInstance.Item) :
    i ∈ D.physicalGlobalPool s ↔
      ∃ j : Fin (D.globalStock s), D.itemEquiv ⟨.«global», ⟨s, j⟩⟩ = i := by
  simp only [physicalGlobalPool, Finset.mem_map, Finset.mem_univ, true_and,
    globalCopyEmbedding_apply]

theorem mem_physicalFlagPool (s : FlagSpecies) (i : D.packingInstance.Item) :
    i ∈ D.physicalFlagPool s ↔
      ∃ j : Fin (D.flagStock s), D.itemEquiv ⟨.flag, ⟨s, j⟩⟩ = i := by
  simp only [physicalFlagPool, Finset.mem_map, Finset.mem_univ, true_and,
    flagCopyEmbedding_apply]

theorem itemEquiv_mem_physicalGlobalPool_iff (a : D.Item) (s : GlobalSpecies D.graph) :
    D.itemEquiv a ∈ D.physicalGlobalPool s ↔
      ∃ j : Fin (D.globalStock s), a = ⟨.«global», ⟨s, j⟩⟩ := by
  rw [mem_physicalGlobalPool]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, (D.itemEquiv.injective hj).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, rfl⟩

theorem itemEquiv_mem_physicalFlagPool_iff (a : D.Item) (s : FlagSpecies) :
    D.itemEquiv a ∈ D.physicalFlagPool s ↔
      ∃ j : Fin (D.flagStock s), a = ⟨.flag, ⟨s, j⟩⟩ := by
  rw [mem_physicalFlagPool]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, (D.itemEquiv.injective hj).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, rfl⟩

@[simp] theorem mem_labeledItems (i : D.packingInstance.Item) :
    i ∈ D.labeledItems ↔
      (D.itemEquiv.symm i).1 = .x ∨ (D.itemEquiv.symm i).1 = .anchor ∨
        (D.itemEquiv.symm i).1 = .«local» := by
  simp [labeledItems]

@[simp] theorem itemEquiv_mem_labeledItems (r : Role) (c : D.RoleCopies r) :
    D.itemEquiv ⟨r, c⟩ ∈ D.labeledItems ↔
      r = .x ∨ r = .anchor ∨ r = .«local» := by
  simp only [mem_labeledItems, Equiv.symm_apply_apply]

@[simp] theorem globalItem_mem_physicalGlobalPool (s t : GlobalSpecies D.graph)
    (j : Fin (D.globalStock s)) :
    D.itemEquiv ⟨.«global», ⟨s, j⟩⟩ ∈ D.physicalGlobalPool t ↔ s = t := by
  rw [itemEquiv_mem_physicalGlobalPool_iff]
  constructor
  · rintro ⟨q, hq⟩
    have hcopy : (⟨s, j⟩ : D.GlobalCopy) = ⟨t, q⟩ :=
      sigma_mk_injective (β := D.RoleCopies) (i := Role.«global») hq
    exact congrArg Sigma.fst hcopy
  · intro h
    subst t
    exact ⟨j, rfl⟩

@[simp] theorem flagItem_mem_physicalFlagPool (s t : FlagSpecies)
    (j : Fin (D.flagStock s)) :
    D.itemEquiv ⟨.flag, ⟨s, j⟩⟩ ∈ D.physicalFlagPool t ↔ s = t := by
  rw [itemEquiv_mem_physicalFlagPool_iff]
  constructor
  · rintro ⟨q, hq⟩
    have hcopy : (⟨s, j⟩ : D.FlagCopy) = ⟨t, q⟩ :=
      sigma_mk_injective (β := D.RoleCopies) (i := Role.flag) hq
    exact congrArg Sigma.fst hcopy
  · intro h
    subst t
    exact ⟨j, rfl⟩

theorem role_eq_global_of_mem_physicalGlobalPool (s : GlobalSpecies D.graph)
    {i : D.packingInstance.Item} (hi : i ∈ D.physicalGlobalPool s) :
    (D.itemEquiv.symm i).1 = .«global» := by
  obtain ⟨j, rfl⟩ := (D.mem_physicalGlobalPool s i).mp hi
  simp only [Equiv.symm_apply_apply]

theorem role_eq_flag_of_mem_physicalFlagPool (s : FlagSpecies)
    {i : D.packingInstance.Item} (hi : i ∈ D.physicalFlagPool s) :
    (D.itemEquiv.symm i).1 = .flag := by
  obtain ⟨j, rfl⟩ := (D.mem_physicalFlagPool s i).mp hi
  simp only [Equiv.symm_apply_apply]

theorem physicalGlobalPool_disjoint {s t : GlobalSpecies D.graph} (hst : s ≠ t) :
    Disjoint (D.physicalGlobalPool s) (D.physicalGlobalPool t) := by
  apply Finset.disjoint_left.mpr
  intro i hi ht
  obtain ⟨j, rfl⟩ := (D.mem_physicalGlobalPool s i).mp hi
  exact hst ((D.globalItem_mem_physicalGlobalPool s t j).mp ht)

theorem physicalFlagPool_disjoint {s t : FlagSpecies} (hst : s ≠ t) :
    Disjoint (D.physicalFlagPool s) (D.physicalFlagPool t) := by
  apply Finset.disjoint_left.mpr
  intro i hi ht
  obtain ⟨j, rfl⟩ := (D.mem_physicalFlagPool s i).mp hi
  exact hst ((D.flagItem_mem_physicalFlagPool s t j).mp ht)

theorem physicalGlobalPool_disjoint_physicalFlagPool
    (s : GlobalSpecies D.graph) (t : FlagSpecies) :
    Disjoint (D.physicalGlobalPool s) (D.physicalFlagPool t) := by
  apply Finset.disjoint_left.mpr
  intro i hi ht
  have h := (D.role_eq_global_of_mem_physicalGlobalPool s hi).symm.trans
    (D.role_eq_flag_of_mem_physicalFlagPool t ht)
  cases h

theorem labeledItems_disjoint_physicalGlobalPool (s : GlobalSpecies D.graph) :
    Disjoint D.labeledItems (D.physicalGlobalPool s) := by
  apply Finset.disjoint_left.mpr
  intro i hi hg
  have hr := D.role_eq_global_of_mem_physicalGlobalPool s hg
  have hl := (D.mem_labeledItems i).mp hi
  simp [hr] at hl

theorem labeledItems_disjoint_physicalFlagPool (s : FlagSpecies) :
    Disjoint D.labeledItems (D.physicalFlagPool s) := by
  apply Finset.disjoint_left.mpr
  intro i hi hf
  have hr := D.role_eq_flag_of_mem_physicalFlagPool s hf
  have hl := (D.mem_labeledItems i).mp hi
  simp [hr] at hl

private theorem not_mem_physicalGlobalPool_of_role_ne (r : Role) (c : D.RoleCopies r)
    (s : GlobalSpecies D.graph) (hr : r ≠ .«global») :
    D.itemEquiv ⟨r, c⟩ ∉ D.physicalGlobalPool s := by
  intro hi
  have h := D.role_eq_global_of_mem_physicalGlobalPool s hi
  exact hr (by simpa only [Equiv.symm_apply_apply] using h)

private theorem not_mem_physicalFlagPool_of_role_ne (r : Role) (c : D.RoleCopies r)
    (s : FlagSpecies) (hr : r ≠ .flag) :
    D.itemEquiv ⟨r, c⟩ ∉ D.physicalFlagPool s := by
  intro hi
  have h := D.role_eq_flag_of_mem_physicalFlagPool s hi
  exact hr (by simpa only [Equiv.symm_apply_apply] using h)

theorem physicalInventory_indicator_partition (i : D.packingInstance.Item) :
    (if i ∈ D.labeledItems then (1 : ℝ) else 0) +
      (∑ s, if i ∈ D.physicalGlobalPool s then (1 : ℝ) else 0) +
      (∑ s, if i ∈ D.physicalFlagPool s then (1 : ℝ) else 0) = 1 := by
  classical
  obtain ⟨⟨r, c⟩, rfl⟩ := D.itemEquiv.surjective i
  cases r with
  | x =>
    simp [not_mem_physicalGlobalPool_of_role_ne, not_mem_physicalFlagPool_of_role_ne]
  | anchor =>
    simp [not_mem_physicalGlobalPool_of_role_ne, not_mem_physicalFlagPool_of_role_ne]
  | «global» =>
    rcases c with ⟨s, j⟩
    have hflag : ∀ t : FlagSpecies,
        D.itemEquiv ⟨.«global», ⟨s, j⟩⟩ ∉ D.physicalFlagPool t := fun t =>
      not_mem_physicalFlagPool_of_role_ne D .«global» ⟨s, j⟩ t (by decide)
    simp [hflag]
  | «local» =>
    simp [not_mem_physicalGlobalPool_of_role_ne, not_mem_physicalFlagPool_of_role_ne]
  | flag =>
    rcases c with ⟨s, j⟩
    have hglobal : ∀ t : GlobalSpecies D.graph,
        D.itemEquiv ⟨.flag, ⟨s, j⟩⟩ ∉ D.physicalGlobalPool t := fun t =>
      not_mem_physicalGlobalPool_of_role_ne D .flag ⟨s, j⟩ t (by decide)
    simp [hglobal]

end BinPackingGap.InventoryData

namespace BinPackingGap
namespace InventoryData

variable (D : InventoryData) {b : ℕ}

def rowPrefixExports (p : Packing D.packingInstance b) (h : ℕ) :=
  LabelConservation.exports D.roleLabelData.anchor D.roleLabelData.row
    (p.roleItemAt D.encodedSubclass .anchor) (p.roleItemAt D.encodedSubclass .x) h

def localPrefixExports (p : Packing D.packingInstance b) (h : ℕ) :=
  LabelConservation.exports D.roleLabelData.anchor D.roleLabelData.localLabel
    (p.roleItemAt D.encodedSubclass .anchor) (p.roleItemAt D.encodedSubclass .«local») h

def outsideAnchorPrefix (p : Packing D.packingInstance b) (h : ℕ) :=
  LabelConservation.prefixOutside D.roleLabelData.anchor
    (p.roleItemAt D.encodedSubclass .anchor) h

def outsideRowPrefix (p : Packing D.packingInstance b) (h : ℕ) :=
  LabelConservation.prefixOutside D.roleLabelData.row
    (p.roleItemAt D.encodedSubclass .x) h

def outsideLocalPrefix (p : Packing D.packingInstance b) (h : ℕ) :=
  LabelConservation.prefixOutside D.roleLabelData.localLabel
    (p.roleItemAt D.encodedSubclass .«local») h

theorem rowPrefixExports_add_outsideRow_eq (p : Packing D.packingInstance b) (h : ℕ) :
    (D.rowPrefixExports p h).card + (D.outsideRowPrefix p h).card =
      (D.outsideAnchorPrefix p h).card := by
  apply LabelConservation.exports_add_outsideRole_eq_outsideAnchor
    D.roleLabelData.anchor D.roleLabelData.row
    (p.roleItemAt D.encodedSubclass .anchor) (p.roleItemAt D.encodedSubclass .x)
    (p.roleItemAt_injective D.encodedSubclass .anchor)
    (p.roleItemAt_injective D.encodedSubclass .x)
  · intro t
    exact (p.roleItemAt_labels_le D.encodedSubclass D.encodedLabel D.roleLabelData
      D.encodedCoordinate D.packingInstance_size_eq D.encodedCoordinate_abs_le_six t).1
  · exact D.roleLabelData_anchor_row_count

theorem localPrefixExports_add_outsideLocal_eq (p : Packing D.packingInstance b) (h : ℕ) :
    (D.localPrefixExports p h).card + (D.outsideLocalPrefix p h).card =
      (D.outsideAnchorPrefix p h).card := by
  apply LabelConservation.exports_add_outsideRole_eq_outsideAnchor
    D.roleLabelData.anchor D.roleLabelData.localLabel
    (p.roleItemAt D.encodedSubclass .anchor) (p.roleItemAt D.encodedSubclass .«local»)
    (p.roleItemAt_injective D.encodedSubclass .anchor)
    (p.roleItemAt_injective D.encodedSubclass .«local»)
  · intro t
    exact (p.roleItemAt_labels_le D.encodedSubclass D.encodedLabel D.roleLabelData
      D.encodedCoordinate D.packingInstance_size_eq D.encodedCoordinate_abs_le_six t).2
  · exact D.roleLabelData_anchor_local_count

theorem rowPrefixExports_eq_outside_sub (p : Packing D.packingInstance b) (h : ℕ) :
    ((D.rowPrefixExports p h).card : ℤ) =
      (D.outsideAnchorPrefix p h).card - (D.outsideRowPrefix p h).card := by
  have heq := D.rowPrefixExports_add_outsideRow_eq p h
  omega

theorem localPrefixExports_eq_outside_sub (p : Packing D.packingInstance b) (h : ℕ) :
    ((D.localPrefixExports p h).card : ℤ) =
      (D.outsideAnchorPrefix p h).card - (D.outsideLocalPrefix p h).card := by
  have heq := D.localPrefixExports_add_outsideLocal_eq p h
  omega

theorem rowPrefixExports_card_lt_lossAllowance {c : ℕ} (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c) (h : ℕ) :
    (D.rowPrefixExports p h).card < lossAllowance c := by
  have heq := D.rowPrefixExports_add_outsideRow_eq p h
  have hprefix : (D.outsideAnchorPrefix p h).card ≤
      (LabelConservation.outsideItems (p.roleItemAt D.encodedSubclass .anchor)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hout := (p.outside_roleItems_card_le D.encodedSubclass .anchor).trans_lt
    (D.outsideTableItems_card_lt_lossAllowance hk p hb)
  omega

theorem localPrefixExports_card_lt_lossAllowance {c : ℕ} (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c) (h : ℕ) :
    (D.localPrefixExports p h).card < lossAllowance c := by
  have heq := D.localPrefixExports_add_outsideLocal_eq p h
  have hprefix : (D.outsideAnchorPrefix p h).card ≤
      (LabelConservation.outsideItems (p.roleItemAt D.encodedSubclass .anchor)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hout := (p.outside_roleItems_card_le D.encodedSubclass .anchor).trans_lt
    (D.outsideTableItems_card_lt_lossAllowance hk p hb)
  omega

end InventoryData
end BinPackingGap

end

end OAI
