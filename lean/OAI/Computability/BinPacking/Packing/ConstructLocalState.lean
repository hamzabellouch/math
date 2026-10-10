import OAI.Computability.BinPacking.Inventory.LocalCompletionCoverage

namespace OAI

noncomputable section

namespace BinPackingGap.InventoryData

def constructedLocalState (G : GraphInput) {d : ℕ} (T : CompetingTrees d)
    (hd : 0 < d) (R k : ℕ) (v : G.Vertex) (selected : Bool) :
    (ofCompetingTrees G T R k).LocalState v selected where
  localEquiv := LocalResourceAllocation.localEquiv G T hd R k v selected
  anchorEquiv := Classical.choose
    (LocalCompletionCoverage.exists_anchorEquiv G T hd R k v selected)
  completion_le_deadline := Classical.choose_spec
    (LocalCompletionCoverage.exists_anchorEquiv G T hd R k v selected)

end BinPackingGap.InventoryData

end

end OAI
