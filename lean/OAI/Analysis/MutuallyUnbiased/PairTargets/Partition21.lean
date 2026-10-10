import Mathlib.Data.Fintype.CardEmbedding
import OAI.Analysis.MutuallyUnbiased.PairTargets.Data
import OAI.Analysis.MutuallyUnbiased.PairTargets.PartitionRules
import OAI.Analysis.MutuallyUnbiased.Moments.SmallPartitions
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound3
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound4
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound13
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound17
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound18
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound20
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Sound42
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical26
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical160
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical239
import OAI.Analysis.MutuallyUnbiased.PairSemantics.Canonical249
import OAI.Analysis.MutuallyUnbiased.PairTargets.ExtraCanonical0
import OAI.Analysis.MutuallyUnbiased.PairTargets.ExtraCanonical1
import OAI.Analysis.MutuallyUnbiased.PairTargets.ExtraCanonical5
import OAI.Analysis.MutuallyUnbiased.PairTargets.ExtraCanonical6

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open MUB6.Certificate.PairSemantics
open scoped BigOperators

def monomialValue21 : Sparse (Fin 909) := [(0, (-1 / 81)), (1, (-5 / 2592)), (2, (-5 / 2592)), (68, (-5 / 216)), (126, (-5 / 108)), (208, (-5 / 36)), (236, (-5 / 36)), (253, (-5 / 36))]

theorem partition21 {H : CMatrix} (hH : IsHadamard H) :
    pairAverage H (fun K => (∏ j, g K (fun u => term21.charges u j)).re) =
      Sparse.eval monomialValue21 (momentVector H) := by
  let A : Matrix Coord (Fin 4) ℤ := term21.charges
  change pairAverage H (fun K => (∏ j : Fin 4, g K (fun u => A u j)).re) = _
  have hp := pair_partition4 hH A
  have hm0 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 0)) =
      Sparse.eval value0 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 0) = raw7982 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7982 hH).trans (sound0 hH)
  have hm1 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 1)) =
      Sparse.eval value232 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 1) = raw5127 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical5127 hH).trans (sound232 hH)
  have hm2 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 2)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 2) = raw7668 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical7668 hH).trans (sound65 hH)
  have hm3 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 3)) =
      Sparse.eval value117 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 3) = raw845 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (canonical845 hH).trans (sound117 hH)
  have hm4 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 4)) =
      Sparse.eval value856 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 4) = extraRaw0 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical0 hH).trans (sound856 hH)
  have hm5 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 5)) =
      Sparse.eval value46 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 5) = extraRaw90 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical90 hH).trans (sound46 hH)
  have hm6 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 6)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 6) = extraRaw92 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical92 hH).trans (sound5 hH)
  have hm7 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 7)) =
      Sparse.eval value1152 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 7) = extraRaw93 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical93 hH).trans (sound1152 hH)
  have hm8 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 8)) =
      Sparse.eval value5 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 8) = extraRaw30 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical30 hH).trans (sound5 hH)
  have hm9 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 9)) =
      Sparse.eval value65 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 9) = extraRaw4 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical4 hH).trans (sound65 hH)
  have hm10 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 10)) =
      Sparse.eval value1151 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 10) = extraRaw94 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical94 hH).trans (sound1151 hH)
  have hm11 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 11)) =
      Sparse.eval value283 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 11) = extraRaw95 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical95 hH).trans (sound283 hH)
  have hm12 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 12)) =
      Sparse.eval value1294 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 12) = extraRaw96 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical96 hH).trans (sound1294 hH)
  have hm13 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 13)) =
      Sparse.eval value858 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 13) = extraRaw91 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical91 hH).trans (sound858 hH)
  have hm14 : injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 14)) =
      Sparse.eval value2711 (momentVector H) := by
    have heq : groupedColumns A (EqualityPatterns.family4.label 14) = extraRaw97 := by
      ext u v; fin_cases u <;> fin_cases v <;> decide +kernel
    rw [heq]
    exact (extraCanonical97 hH).trans (sound2711 hH)
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14] at hp
  norm_num [Fintype.card_embedding_eq, Coord, EqualityPatterns.family4, EqualityPatterns.blocks4, Nat.descFactorial, monomialValue21, value0, value1151, value1152, value117, value1294, value232, value2711, value283, value46, value5, value65, value856, value858, Sparse.eval] at hp ⊢
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
