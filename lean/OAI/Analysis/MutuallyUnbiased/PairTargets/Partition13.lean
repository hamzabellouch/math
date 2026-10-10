import Mathlib.Data.Fintype.CardEmbedding
import OAI.Analysis.MutuallyUnbiased.PairTargets.Data
import OAI.Analysis.MutuallyUnbiased.PairTargets.PartitionRules
import OAI.Analysis.MutuallyUnbiased.Moments.SmallPartitions
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound8
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound11
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound34
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical161
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairTargets.ExtraCanonical0
import OAI.Analysis.MutuallyUnbiased.PairTargets.ExtraCanonical2
import OAI.Analysis.MutuallyUnbiased.PairTargets.ExtraCanonical3

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue13 : Sparse (Fin 909) := [(0, (5 / 1728)), (1, (-5 / 576)), (2, (5 / 2592)), (4, (5 / 324)), (31, (-5 / 108)), (68, (-5 / 216)), (126, (-5 / 36)), (207, (-5 / 36)), (208, (-5 / 36)), (236, (-5 / 108))]

theorem partition13 {H : CMatrix} (hH : IsHadamard H) :
    pairAverage H (fun K => (∏ j, g K (fun u => term13.charges u j)).re) =
      Sparse.eval monomialValue13 (momentVector H) := by
  let A : Matrix Coord (Fin 4) ℤ := term13.charges
  change pairAverage H (fun K => (∏ j : Fin 4, g K (fun u => A u j)).re) = _
  have hp := pair_partition4 hH A
  have hm0 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 0)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 0) = raw7982 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7982 hH).trans (sound0 hH)
  have hm1 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 1)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 1) = raw5124 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical5124 hH).trans (sound46 hH)
  have hm2 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 2)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 2) = extraRaw2 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical2 hH).trans (sound65 hH)
  have hm3 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 3)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 3) = raw845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical845 hH).trans (sound117 hH)
  have hm4 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 4)) =
      Sparse.eval value858 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 4) = extraRaw3 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical3 hH).trans (sound858 hH)
  have hm5 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 5)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 5) = extraRaw35 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical35 hH).trans (sound232 hH)
  have hm6 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 6)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 6) = extraRaw49 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical49 hH).trans (sound65 hH)
  have hm7 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 7)) =
      Sparse.eval value1141 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 7) = extraRaw50 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical50 hH).trans (sound1141 hH)
  have hm8 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 8)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 8) = extraRaw51 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical51 hH).trans (sound5 hH)
  have hm9 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 9)) =
      Sparse.eval value11 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 9) = raw5164 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical5164 hH).trans (sound11 hH)
  have hm10 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 10)) =
      Sparse.eval value284 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 10) = extraRaw52 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical52 hH).trans (sound284 hH)
  have hm11 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 11)) =
      Sparse.eval value1151 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 11) = extraRaw53 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical53 hH).trans (sound1151 hH)
  have hm12 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 12)) =
      Sparse.eval value711 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 12) = extraRaw54 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical54 hH).trans (sound711 hH)
  have hm13 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 13)) =
      Sparse.eval value545 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 13) = extraRaw36 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical36 hH).trans (sound545 hH)
  have hm14 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 14)) =
      Sparse.eval value2204 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 14) = extraRaw55 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical55 hH).trans (sound2204 hH)
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14] at hp
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family4, EqualityPatterns.blocks4, Nat.descFactorial, monomialValue13, value0, value11, value1141, value1151, value117, value2204, value232, value284, value46, value5, value545, value65, value711, value858, Sparse.eval] at hp ⊢
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
