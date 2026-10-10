import OAI.Computability.BinPacking.Arithmetic.GraphTallyMachine
import OAI.Computability.BinPacking.Packing.ExtractedCover
import OAI.Computability.BinPacking.Packing.ItemEnumeration
import OAI.Computability.BinPacking.Packing.PackingScalarExpression

namespace OAI

noncomputable section

namespace BinPackingGap.InventoryData

variable (D : InventoryData)

def rawItemList : RawInstance := D.itemList.map D.itemRawPair

theorem rawItemList_length_items : D.rawItemList.length = D.itemList.length := by
  simp [rawItemList]

theorem rawItemList_length (hk : D.k ≤ D.graph.n) :
    D.rawItemList.length = 5 * D.B := by
  rw [D.rawItemList_length_items, D.itemList_length hk]

theorem rawItemList_valid (hplus : D.plus.height ≤ D.L)
    (hminus : D.minus.height ≤ D.L) : D.rawItemList.Valid := by
  intro q hq
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
  have hi := D.itemRawPair_valid hplus hminus i
  exact ⟨hi.1, hi.2.le⟩

def rawItemListEquiv (hk : D.k ≤ D.graph.n) : Fin D.rawItemList.length ≃ D.Item :=
  (finCongr D.rawItemList_length_items).trans (D.itemListEquiv hk)

@[simp] theorem rawItemListEquiv_apply (hk : D.k ≤ D.graph.n)
    (i : Fin D.rawItemList.length) :
    D.rawItemListEquiv hk i =
      D.itemList.get (Fin.cast D.rawItemList_length_items i) := rfl

theorem rawItemList_get (i : Fin D.rawItemList.length) :
    D.rawItemList.get i =
      D.itemRawPair (D.itemList.get (Fin.cast D.rawItemList_length_items i)) := by
  rcases i with ⟨i, hi⟩
  change i < (D.itemList.map D.itemRawPair).length at hi
  change (D.itemList.map D.itemRawPair)[i]'hi =
    D.itemRawPair (D.itemList[i]'(by simpa [rawItemList] using hi))
  simp only [List.getElem_map]

theorem rawItemList_get_ratio (hplus : D.plus.height ≤ D.L)
    (hminus : D.minus.height ≤ D.L) (i : Fin D.rawItemList.length) :
    RawInstance.ratValue (D.rawItemList.get i) =
      D.itemSize (D.itemList.get (Fin.cast D.rawItemList_length_items i)) := by
  rw [D.rawItemList_get]
  exact D.itemRawPair_ratio hplus hminus _

def rawItemListReindexing (hk : D.k ≤ D.graph.n)
    (hplus : D.plus.height ≤ D.L) (hminus : D.minus.height ≤ D.L) :
    Instance.Reindexing (D.rawItemList.toInstance (D.rawItemList_valid hplus hminus))
      D.packingInstance where
  equiv := (D.rawItemListEquiv hk).trans D.itemEquiv
  size_eq i := by
    change Fin D.rawItemList.length at i
    change RawInstance.ratValue (D.rawItemList.get i) =
      D.itemSize (D.itemEquiv.symm (D.itemEquiv (D.rawItemListEquiv hk i)))
    rw [Equiv.symm_apply_apply, D.rawItemListEquiv_apply]
    exact D.rawItemList_get_ratio hplus hminus i

theorem rawItemList_hasPacking_iff (hk : D.k ≤ D.graph.n)
    (hplus : D.plus.height ≤ D.L) (hminus : D.minus.height ≤ D.L) (b : ℕ) :
    HasPacking (D.rawItemList.toInstance (D.rawItemList_valid hplus hminus)) b ↔
      HasPacking D.packingInstance b :=
  (D.rawItemListReindexing hk hplus hminus).hasPacking_iff b

theorem rawItemList_opt_eq (hk : D.k ≤ D.graph.n)
    (hplus : D.plus.height ≤ D.L) (hminus : D.minus.height ≤ D.L) :
    opt (D.rawItemList.toInstance (D.rawItemList_valid hplus hminus)) =
      opt D.packingInstance :=
  (D.rawItemListReindexing hk hplus hminus).opt_eq

def rawOutput : RawReductionOutput := (D.B, D.rawItemList)

@[simp] theorem rawOutput_bins : D.rawOutput.1 = D.B := rfl

@[simp] theorem rawOutput_items : D.rawOutput.2 = D.rawItemList := rfl

theorem rawOutput_valid (hplus : D.plus.height ≤ D.L)
    (hminus : D.minus.height ≤ D.L) : D.rawOutput.2.Valid :=
  D.rawItemList_valid hplus hminus

theorem rawOutput_length (hk : D.k ≤ D.graph.n) :
    D.rawOutput.2.length = 5 * D.rawOutput.1 := D.rawItemList_length hk

end BinPackingGap.InventoryData

namespace BinPackingGap

def graphPackingOutput (c : ℕ) (ρ : ℝ) (x : GraphReductionInput) : RawReductionOutput :=
  (reductionInventory c ρ x.graph x.k).rawOutput

@[simp] theorem graphPackingOutput_bins (c : ℕ) (ρ : ℝ) (x : GraphReductionInput) :
    (graphPackingOutput c ρ x).1 = reductionBinBound c ρ x.graph x.k := rfl

theorem graphPackingOutput_valid (c : ℕ) (ρ : ℝ) (x : GraphReductionInput) :
    (graphPackingOutput c ρ x).2.Valid :=
  (reductionInventory c ρ x.graph x.k).rawOutput_valid
    (reductionInventory_plus_height c ρ x.graph x.k).le
    (reductionInventory_minus_height c ρ x.graph x.k).le

theorem graphPackingOutput_length (c : ℕ) (ρ : ℝ) (x : GraphReductionInput) :
    (graphPackingOutput c ρ x).2.length = 5 * (graphPackingOutput c ρ x).1 :=
  (reductionInventory c ρ x.graph x.k).rawOutput_length x.k_le

def graphPackingOutputInstance (c : ℕ) (ρ : ℝ) (x : GraphReductionInput) : Instance :=
  (graphPackingOutput c ρ x).2.toInstance (graphPackingOutput_valid c ρ x)

def graphPackingOutputReindexing (c : ℕ) (ρ : ℝ) (x : GraphReductionInput) :
    Instance.Reindexing (graphPackingOutputInstance c ρ x)
      (reductionInstance c ρ x.graph x.k) :=
  (reductionInventory c ρ x.graph x.k).rawItemListReindexing x.k_le
    (reductionInventory_plus_height c ρ x.graph x.k).le
    (reductionInventory_minus_height c ρ x.graph x.k).le

theorem graphPackingOutput_count (c : ℕ) (ρ : ℝ) (x : GraphReductionInput) :
    (graphPackingOutputInstance c ρ x).n = 5 * (graphPackingOutput c ρ x).1 :=
  graphPackingOutput_length c ρ x

theorem graphPackingOutput_size_bounds (c : ℕ) (ρ : ℝ) (x : GraphReductionInput)
    (i : (graphPackingOutputInstance c ρ x).Item) :
    (1 / 6 : ℚ) < (graphPackingOutputInstance c ρ x).size i ∧
      (graphPackingOutputInstance c ρ x).size i < 1 := by
  rw [(graphPackingOutputReindexing c ρ x).size_eq i]
  exact reductionInstance_size_bounds c ρ x.graph x.k _

theorem graphPackingOutput_hasPacking_iff (c : ℕ) (ρ : ℝ)
    (x : GraphReductionInput) (b : ℕ) :
    HasPacking (graphPackingOutputInstance c ρ x) b ↔
      HasPacking (reductionInstance c ρ x.graph x.k) b :=
  (graphPackingOutputReindexing c ρ x).hasPacking_iff b

theorem graphPackingOutput_opt_eq (c : ℕ) (ρ : ℝ) (x : GraphReductionInput) :
    opt (graphPackingOutputInstance c ρ x) =
      opt (reductionInstance c ρ x.graph x.k) :=
  (graphPackingOutputReindexing c ρ x).opt_eq

end BinPackingGap

end

end OAI
