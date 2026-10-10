import Mathlib.Data.Fintype.CardEmbedding
import OAI.Analysis.MutuallyUnbiased.PairTargets.Data
import OAI.Analysis.MutuallyUnbiased.PairTargets.PartitionRules
import OAI.Analysis.MutuallyUnbiased.Moments.SmallPartitions
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue0 : Sparse (Fin 909) := [(0, (1 / 6)), (1, (-5 / 72)), (2, (-5 / 72)), (5, (5 / 36)), (27, (-5 / 12)), (68, (-5 / 6))]

theorem partition0 {H : CMatrix} (hH : IsHadamard H) :
    pairAverage H (fun K => (∏ j, g K (fun u => term0.charges u j)).re) =
      Sparse.eval monomialValue0 (momentVector H) := by
  let A : Matrix Coord (Fin 2) ℤ := term0.charges
  change pairAverage H (fun K => (∏ j : Fin 2, g K (fun u => A u j)).re) = _
  have hp := pair_partition2 hH A
  have hm0 : injectiveMoment H (groupedColumns A (EqualityPatterns.family2.label 0)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family2.label 0) = raw7982 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7982 hH).trans (sound0 hH)
  have hm1 : injectiveMoment H (groupedColumns A (EqualityPatterns.family2.label 1)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family2.label 1) = raw845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical845 hH).trans (sound117 hH)
  rw [hm0, hm1] at hp
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family2, EqualityPatterns.blocks2, Nat.descFactorial, monomialValue0, value0, value117, Sparse.eval] at hp ⊢
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
