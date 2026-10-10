import OAI.Computability.BinPacking.Inventory.InventoryScores
import OAI.Computability.BinPacking.Trees.TreeColorCounts

namespace OAI

namespace BinPackingGap.InventoryData

def ofCompetingTrees (G : GraphInput) {d : ℕ} (T : CompetingTrees d) (R k : ℕ) :
    InventoryData where
  graph := G
  plus := T.plus
  minus := T.minus
  d := d
  R := R
  L := T.height
  quota := T.quota
  k := k

@[simp] theorem ofCompetingTrees_P (G : GraphInput) {d : ℕ}
    (T : CompetingTrees d) (R k : ℕ) :
    (ofCompetingTrees G T R k).P = T.quotaTotal := rfl

theorem ofCompetingTrees_plus_height (G : GraphInput) {d : ℕ}
    (T : CompetingTrees d) (R k : ℕ) :
    (ofCompetingTrees G T R k).plus.height = (ofCompetingTrees G T R k).L :=
  T.plus_height

theorem ofCompetingTrees_minus_height (G : GraphInput) {d : ℕ}
    (T : CompetingTrees d) (R k : ℕ) :
    (ofCompetingTrees G T R k).minus.height = (ofCompetingTrees G T R k).L :=
  T.minus_height

theorem ofCompetingTrees_height_pos (G : GraphInput) {d : ℕ}
    (T : CompetingTrees d) (R k : ℕ) : 0 < (ofCompetingTrees G T R k).L :=
  T.height_pos

end BinPackingGap.InventoryData

end OAI
