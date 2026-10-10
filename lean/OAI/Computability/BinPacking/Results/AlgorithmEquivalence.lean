import OAI.Computability.BinPacking.Results.AdditiveHardness
import OAI.Computability.BinPacking.Results.OptimalSearch
import OAI.Computability.BinPacking.Results.StructuralGap

namespace OAI

namespace BinPackingGap

theorem exists_absoluteAdditiveAlgorithm_iff_pEqualsNP :
    (∃ c : Nat, Nonempty (AbsoluteAdditiveAlgorithm c)) ↔ PEqualsNP := by
  constructor
  · exact pEqualsNP_of_exists_absoluteAdditiveAlgorithm
  · intro equality
    exact ⟨0, ⟨absoluteAdditiveAlgorithm_of_pEqualsNP equality⟩⟩

end BinPackingGap

end OAI
