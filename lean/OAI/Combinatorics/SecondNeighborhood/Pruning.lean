import OAI.Combinatorics.SecondNeighborhood.AugmentedRankBound
import OAI.Combinatorics.SecondNeighborhood.CoverPruning

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem pruning (r : X → X → Prop) : PruningStatement r := by
  intro R C
  obtain ⟨M, hM, hα, hβ⟩ := exists_augmented_maximum_matching r R C
  apply exists_pruning_of_augmented_matching_bound r R C M hM
  simpa only [Nat.add_comm] using
    augmented_matching_card_le_corners r R C M hM.1 hα hβ

end SeymourSecondNeighborhood.Pruning

end OAI
