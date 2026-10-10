import Mathlib.Data.Fintype.CardEmbedding
import OAI.Analysis.MutuallyUnbiased.PairMoments.PairAverage
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.FiniteSums
import OAI.Analysis.MutuallyUnbiased.Moments.SmallPartitions

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open scoped BigOperators

theorem sum_fin_fifteen {α : Type*} [AddCommMonoid α] (f : Fin 15 → α) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + 0)))))))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12 + f 13 + f 14
  ac_rfl

theorem partitionWeight2_0 :
    (Fintype.card (Fin (EqualityPatterns.family2.blocks 0) ↪ Coord) : ℝ) / 6 ^ 2 = (1/6 : ℝ) := by
  change (Fintype.card (Fin 1 ↪ Fin 6) : ℝ) / 6 ^ 2 = (1/6 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight2_1 :
    (Fintype.card (Fin (EqualityPatterns.family2.blocks 1) ↪ Coord) : ℝ) / 6 ^ 2 = (5/6 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 2 = (5/6 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem pair_partition2 {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix Coord (Fin 2) ℤ) :
    pairAverage H (fun K => (∏ j, g K (fun u => A u j)).re) =
      (1 / 6 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family2.label 0)) +
      (5 / 6 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family2.label 1)) := by
  have h := pairAverage_products_partition hH A EqualityPatterns.family2 EqualityPatterns.covers2
  rw [MixedSemantics.sum_fin_two] at h
  simpa only [partitionWeight2_0, partitionWeight2_1] using h

theorem partitionWeight3_0 :
    (Fintype.card (Fin (EqualityPatterns.family3.blocks 0) ↪ Coord) : ℝ) / 6 ^ 3 = (1/36 : ℝ) := by
  change (Fintype.card (Fin 1 ↪ Fin 6) : ℝ) / 6 ^ 3 = (1/36 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight3_1 :
    (Fintype.card (Fin (EqualityPatterns.family3.blocks 1) ↪ Coord) : ℝ) / 6 ^ 3 = (5/36 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 3 = (5/36 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight3_2 :
    (Fintype.card (Fin (EqualityPatterns.family3.blocks 2) ↪ Coord) : ℝ) / 6 ^ 3 = (5/36 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 3 = (5/36 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight3_3 :
    (Fintype.card (Fin (EqualityPatterns.family3.blocks 3) ↪ Coord) : ℝ) / 6 ^ 3 = (5/36 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 3 = (5/36 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight3_4 :
    (Fintype.card (Fin (EqualityPatterns.family3.blocks 4) ↪ Coord) : ℝ) / 6 ^ 3 = (5/9 : ℝ) := by
  change (Fintype.card (Fin 3 ↪ Fin 6) : ℝ) / 6 ^ 3 = (5/9 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem pair_partition3 {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix Coord (Fin 3) ℤ) :
    pairAverage H (fun K => (∏ j, g K (fun u => A u j)).re) =
      (1 / 36 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 0)) +
      (5 / 36 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 1)) +
      (5 / 36 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 2)) +
      (5 / 36 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 3)) +
      (5 / 9 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family3.label 4)) := by
  have h := pairAverage_products_partition hH A EqualityPatterns.family3 EqualityPatterns.covers3
  rw [MixedSemantics.sum_fin_five] at h
  simpa only [partitionWeight3_0, partitionWeight3_1, partitionWeight3_2, partitionWeight3_3, partitionWeight3_4] using h

theorem partitionWeight4_0 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 0) ↪ Coord) : ℝ) / 6 ^ 4 = (1/216 : ℝ) := by
  change (Fintype.card (Fin 1 ↪ Fin 6) : ℝ) / 6 ^ 4 = (1/216 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_1 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 1) ↪ Coord) : ℝ) / 6 ^ 4 = (5/216 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/216 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_2 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 2) ↪ Coord) : ℝ) / 6 ^ 4 = (5/216 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/216 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_3 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 3) ↪ Coord) : ℝ) / 6 ^ 4 = (5/216 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/216 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_4 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 4) ↪ Coord) : ℝ) / 6 ^ 4 = (5/54 : ℝ) := by
  change (Fintype.card (Fin 3 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/54 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_5 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 5) ↪ Coord) : ℝ) / 6 ^ 4 = (5/216 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/216 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_6 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 6) ↪ Coord) : ℝ) / 6 ^ 4 = (5/216 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/216 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_7 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 7) ↪ Coord) : ℝ) / 6 ^ 4 = (5/54 : ℝ) := by
  change (Fintype.card (Fin 3 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/54 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_8 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 8) ↪ Coord) : ℝ) / 6 ^ 4 = (5/216 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/216 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_9 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 9) ↪ Coord) : ℝ) / 6 ^ 4 = (5/216 : ℝ) := by
  change (Fintype.card (Fin 2 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/216 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_10 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 10) ↪ Coord) : ℝ) / 6 ^ 4 = (5/54 : ℝ) := by
  change (Fintype.card (Fin 3 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/54 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_11 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 11) ↪ Coord) : ℝ) / 6 ^ 4 = (5/54 : ℝ) := by
  change (Fintype.card (Fin 3 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/54 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_12 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 12) ↪ Coord) : ℝ) / 6 ^ 4 = (5/54 : ℝ) := by
  change (Fintype.card (Fin 3 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/54 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_13 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 13) ↪ Coord) : ℝ) / 6 ^ 4 = (5/54 : ℝ) := by
  change (Fintype.card (Fin 3 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/54 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem partitionWeight4_14 :
    (Fintype.card (Fin (EqualityPatterns.family4.blocks 14) ↪ Coord) : ℝ) / 6 ^ 4 = (5/18 : ℝ) := by
  change (Fintype.card (Fin 4 ↪ Fin 6) : ℝ) / 6 ^ 4 = (5/18 : ℝ)
  norm_num [Fintype.card_embedding_eq, Nat.descFactorial]

theorem pair_partition4 {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix Coord (Fin 4) ℤ) :
    pairAverage H (fun K => (∏ j, g K (fun u => A u j)).re) =
      (1 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 0)) +
      (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 1)) +
      (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 2)) +
      (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 3)) +
      (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 4)) +
      (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 5)) +
      (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 6)) +
      (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 7)) +
      (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 8)) +
      (5 / 216 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 9)) +
      (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 10)) +
      (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 11)) +
      (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 12)) +
      (5 / 54 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 13)) +
      (5 / 18 : ℝ) * injectiveMoment H (groupedColumns A (EqualityPatterns.family4.label 14)) := by
  have h := pairAverage_products_partition hH A EqualityPatterns.family4 EqualityPatterns.covers4
  rw [sum_fin_fifteen] at h
  simpa only [partitionWeight4_0, partitionWeight4_1, partitionWeight4_2, partitionWeight4_3, partitionWeight4_4, partitionWeight4_5, partitionWeight4_6, partitionWeight4_7, partitionWeight4_8, partitionWeight4_9, partitionWeight4_10, partitionWeight4_11, partitionWeight4_12, partitionWeight4_13, partitionWeight4_14] using h

end MUB6.Certificate.PairTargetSemantics

end OAI
