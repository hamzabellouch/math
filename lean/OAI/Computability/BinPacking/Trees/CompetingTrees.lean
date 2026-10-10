import OAI.Computability.BinPacking.Packing.PhaseIteration

namespace OAI

namespace BinPackingGap

def competingTrees (d : ℕ) (hd : 0 < d) : CompetingTrees d :=
  CompetingTrees.ofAuxiliary d hd (buildAuxiliary (2 * d - 1))

theorem exists_competingTrees (d : ℕ) (hd : 0 < d) : Nonempty (CompetingTrees d) :=
  ⟨competingTrees d hd⟩

end BinPackingGap

end OAI
