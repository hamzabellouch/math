import Mathlib.Data.Fintype.CardEmbedding
import OAI.Analysis.MutuallyUnbiased.PairTargets.Data
import OAI.Analysis.MutuallyUnbiased.PairTargets.PartitionRules
import OAI.Analysis.MutuallyUnbiased.Moments.SmallPartitions
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical239
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairTargets.ExtraCanonical0

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue1 : Sparse (Fin 909) := [(0, (7 / 216)), (1, (25 / 432)), (2, (-5 / 432)), (5, (5 / 216)), (8, (5 / 54)), (27, (-5 / 72)), (30, (-5 / 18)), (68, (-5 / 36)), (236, (-5 / 9))]

theorem partition1 {H : CMatrix} (hH : IsHadamard H) :
    pairAverage H (fun K => (∏ j, g K (fun u => term1.charges u j)).re) =
      Sparse.eval monomialValue1 (momentVector H) := by
  let A : Matrix Coord (Fin 3) ℤ := term1.charges
  change pairAverage H (fun K => (∏ j : Fin 3, g K (fun u => A u j)).re) = _
  have hp := pair_partition3 hH A
  have hm0 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 0)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 0) = raw7982 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7982 hH).trans (sound0 hH)
  have hm1 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 1)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 1) = raw5127 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical5127 hH).trans (sound232 hH)
  have hm2 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 2)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 2) = raw7668 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7668 hH).trans (sound65 hH)
  have hm3 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 3)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 3) = raw845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical845 hH).trans (sound117 hH)
  have hm4 : injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 4)) =
      Sparse.eval value856 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family3.label 4) = extraRaw0 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical0 hH).trans (sound856 hH)
  rw [hm0, hm1, hm2, hm3, hm4] at hp
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family3, EqualityPatterns.blocks3, Nat.descFactorial, monomialValue1, value0, value117, value232, value65, value856, Sparse.eval] at hp ⊢
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
