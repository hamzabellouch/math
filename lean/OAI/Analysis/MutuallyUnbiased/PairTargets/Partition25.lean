import Mathlib.Data.Fintype.CardEmbedding
import OAI.Analysis.MutuallyUnbiased.PairTargets.Data
import OAI.Analysis.MutuallyUnbiased.PairTargets.PartitionRules
import OAI.Analysis.MutuallyUnbiased.Moments.SmallPartitions
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound5
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound29
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound36
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound51
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical283
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical316
import OAI.Analysis.MutuallyUnbiased.PairTargets.ExtraCanonical7

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue25 : Sparse (Fin 909) := [(0, (-1 / 144)), (1, (-185 / 1296)), (2, (5 / 192)), (3, (-5 / 27)), (5, (-5 / 108)), (6, (-5 / 1296)), (7, (-10 / 81)), (12, (-10 / 81)), (23, (-5 / 27)), (27, (-5 / 108)), (58, (5 / 5184)), (68, (5 / 216)), (69, (-5 / 81)), (230, (5 / 36))]

theorem partition25 {H : CMatrix} (hH : IsHadamard H) :
    pairAverage H (fun K => (∏ j, g K (fun u => term25.charges u j)).re) =
      Sparse.eval monomialValue25 (momentVector H) := by
  let A : Matrix Coord (Fin 4) ℤ := term25.charges
  change pairAverage H (fun K => (∏ j : Fin 4, g K (fun u => A u j)).re) = _
  have hp := pair_partition4 hH A
  have hm0 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 0)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 0) = raw7982 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7982 hH).trans (sound0 hH)
  have hm1 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 1)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 1) = extraRaw116 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical116 hH).trans (sound4 hH)
  have hm2 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 2)) =
      Sparse.eval value1323 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 2) = raw10113 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10113 hH).trans (sound1323 hH)
  have hm3 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 3)) =
      Sparse.eval value381 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 3) = extraRaw117 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical117 hH).trans (sound381 hH)
  have hm4 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 4)) =
      Sparse.eval value1873 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 4) = extraRaw118 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical118 hH).trans (sound1873 hH)
  have hm5 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 5)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 5) = extraRaw119 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical119 hH).trans (sound4 hH)
  have hm6 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 6)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 6) = raw9056 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical9056 hH).trans (sound0 hH)
  have hm7 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 7)) =
      Sparse.eval value4 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 7) = extraRaw120 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical120 hH).trans (sound4 hH)
  have hm8 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 8)) =
      Sparse.eval value1323 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 8) = extraRaw121 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical121 hH).trans (sound1323 hH)
  have hm9 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 9)) =
      Sparse.eval value1323 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 9) = raw10113 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical10113 hH).trans (sound1323 hH)
  have hm10 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 10)) =
      Sparse.eval value2304 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 10) = extraRaw122 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical122 hH).trans (sound2304 hH)
  have hm11 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 11)) =
      Sparse.eval value2304 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 11) = extraRaw123 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical123 hH).trans (sound2304 hH)
  have hm12 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 12)) =
      Sparse.eval value1323 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 12) = extraRaw124 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical124 hH).trans (sound1323 hH)
  have hm13 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 13)) =
      Sparse.eval value1873 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 13) = extraRaw125 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical125 hH).trans (sound1873 hH)
  have hm14 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 14)) =
      Sparse.eval value3317 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 14) = extraRaw126 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical126 hH).trans (sound3317 hH)
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14] at hp
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family4, EqualityPatterns.blocks4, Nat.descFactorial, monomialValue25, value0, value1323, value1873, value2304, value3317, value381, value4, Sparse.eval] at hp ⊢
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
