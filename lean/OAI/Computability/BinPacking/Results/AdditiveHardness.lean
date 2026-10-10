import OAI.Computability.BinPacking.Results.PackingHardness
import OAI.Computability.BinPacking.Search.ApproximationImpliesP

namespace OAI

namespace BinPackingGap

theorem pEqualsNP_of_absoluteAdditiveAlgorithm (c : Nat)
    (algorithm : AbsoluteAdditiveAlgorithm c) : PEqualsNP :=
  (packingGapNPHard c).pEqualsNP_of_absoluteAdditiveAlgorithm algorithm

theorem pEqualsNP_of_exists_absoluteAdditiveAlgorithm
    (h : ∃ c : Nat, Nonempty (AbsoluteAdditiveAlgorithm c)) : PEqualsNP := by
  obtain ⟨c, ⟨algorithm⟩⟩ := h
  exact pEqualsNP_of_absoluteAdditiveAlgorithm c algorithm

end BinPackingGap

end OAI
