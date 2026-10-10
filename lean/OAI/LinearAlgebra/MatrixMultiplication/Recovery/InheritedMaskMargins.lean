import OAI.LinearAlgebra.MatrixMultiplication.Recovery.InheritedMaskConcentration
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.InheritedMasks
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.InheritedStatisticWindows

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators
open MatrixMultiplication.InheritedMasks
open Classical

noncomputable section

section ClassMixtures

variable {C : Type*} [Fintype C] [DecidableEq C] {P : C → Type*}
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]

def classWeight (P : C → Type*) [∀ c, Fintype (P c)] (c : C) : ℝ :=
  (Fintype.card (P c) : ℝ) / populationSize P

def classDensity (A : ∀ c, Finset (P c)) (c : C) : ℝ :=
  ((A c).card : ℝ) / Fintype.card (P c)

def classProductMixture (P : C → Type*) [∀ c, Fintype (P c)]
    (left right : C → ℝ) : ℝ :=
  ∑ c, classWeight P c * (left c * right c)

omit [DecidableEq C] [∀ c, DecidableEq (P c)] in
theorem classWeight_nonneg (hm : 0 < populationSize P) (c : C) :
    0 ≤ classWeight P c := div_nonneg (Nat.cast_nonneg _) (le_of_lt hm)

omit [DecidableEq C] [∀ c, DecidableEq (P c)] in
theorem sum_classWeight (hm : 0 < populationSize P) :
    ∑ c, classWeight P c = 1 := by
  unfold classWeight
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hm)

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (P c)] in
theorem classDensity_nonneg (A : ∀ c, Finset (P c)) (c : C) :
    0 ≤ classDensity A c := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (P c)] in
theorem classDensity_le_one [∀ c, Nonempty (P c)]
    (A : ∀ c, Finset (P c)) (c : C) : classDensity A c ≤ 1 := by
  have hn : (0 : ℝ) < Fintype.card (P c) := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hn).2
  simpa using (Nat.cast_le.mpr (Finset.card_le_univ (A c)) :
    ((A c).card : ℝ) ≤ Fintype.card (P c))

omit [DecidableEq C] in
theorem totalMatchingMean_normalized_eq [∀ c, Nonempty (P c)]
    (A B : ∀ c, Finset (P c)) (hm : 0 < populationSize P) :
    totalMatchingMean A B / populationSize P =
      classProductMixture P (classDensity A) (classDensity B) := by
  classical
  rw [totalMatchingMean_eq, Finset.sum_div]
  unfold classProductMixture
  apply Finset.sum_congr rfl
  intro c _
  have hn : (Fintype.card (P c) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos (α := P c)))
  dsimp [classWeight, classDensity]
  field_simp [hn, ne_of_gt hm]

omit [DecidableEq C] in
theorem totalMatchingMean_prescribed_error [∀ c, Nonempty (P c)]
    (A B : ∀ c, Finset (P c)) (hm : 0 < populationSize P)
    (left right : C → ℝ) (τ : ℝ)
    (hright0 : ∀ c, 0 ≤ right c) (hright1 : ∀ c, right c ≤ 1)
    (hleft : ∀ c, |classDensity A c - left c| ≤ τ)
    (hright : ∀ c, |classDensity B c - right c| ≤ τ) :
    |totalMatchingMean A B / populationSize P -
      classProductMixture P left right| ≤ 2 * τ := by
  rw [totalMatchingMean_normalized_eq A B hm]
  have h := weighted_window (classWeight P)
    (fun c => classDensity A c * classDensity B c - left c * right c)
    0 (2 * τ) (classWeight_nonneg hm) (sum_classWeight hm) (by
      intro c
      simpa only [sub_zero] using product_coordinate_error
        (classDensity_nonneg A c) (classDensity_le_one A c)
        (hright0 c) (hright1 c) (hleft c) (hright c))
  simpa only [classProductMixture, sub_zero, mul_sub, Finset.sum_sub_distrib] using h

omit [DecidableEq C] in
theorem totalMatchingMean_inherited_margin [∀ c, Nonempty (P c)]
    (A B : ∀ c, Finset (P c)) (hm : 0 < populationSize P)
    (left right : C → ℝ) (η τ α ν : ℝ)
    (hright0 : ∀ c, 0 ≤ right c) (hright1 : ∀ c, right c ≤ 1)
    (hleft : ∀ c, |classDensity A c - left c| ≤ τ)
    (hright : ∀ c, |classDensity B c - right c| ≤ τ)
    (happrox : |classProductMixture P left right - ν| ≤ α)
    (hτ : τ ≤ η / 8) (hα : α ≤ η / 4) :
    |totalMatchingMean A B / populationSize P - ν| ≤ η / 2 := by
  have hchild := totalMatchingMean_prescribed_error A B hm left right τ
    hright0 hright1 hleft hright
  have h := inherited_margin (actual := ν)
    (expected := classProductMixture P left right)
    (prescribed := totalMatchingMean A B / populationSize P)
    (by simpa only [abs_sub_comm] using hchild)
    (by simpa only [abs_sub_comm] using happrox) hτ hα
  simpa only [abs_sub_comm] using h

theorem inheritedMask_rejection_of_windows_le [∀ c, Nonempty (P c)]
    (A B : ∀ c, Finset (P c)) (hn : ∀ c, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize P) (left right : C → ℝ) (η τ α ν : ℝ)
    (hη : 0 < η)
    (hright0 : ∀ c, 0 ≤ right c) (hright1 : ∀ c, right c ≤ 1)
    (hleft : ∀ c, |classDensity A c - left c| ≤ τ)
    (hright : ∀ c, |classDensity B c - right c| ≤ τ)
    (happrox : |classProductMixture P left right - ν| ≤ α)
    (hτ : τ ≤ η / 8) (hα : α ≤ η / 4) :
    average (fun p : ClassPermutations P =>
      if η < |totalMatchingCount A B p / populationSize P - ν| then 1 else 0) ≤
        1 / (2 * populationSize P * η ^ 2) := by
  exact inheritedMask_rejection_le A B hn hm η ν hη
    (totalMatchingMean_inherited_margin A B hm left right η τ α ν
      hright0 hright1 hleft hright happrox hτ hα)

theorem twoHalf_inheritedMask_rejection_of_windows_le [∀ c, Nonempty (P c)]
    (A B : ∀ c, Finset (P c)) (hn : ∀ c, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize P) (left right : C → ℝ) (η τ α ν : ℝ)
    (hη : 0 < η)
    (hright0 : ∀ c, 0 ≤ right c) (hright1 : ∀ c, right c ≤ 1)
    (hleft : ∀ c, |classDensity A c - left c| ≤ τ)
    (hright : ∀ c, |classDensity B c - right c| ≤ τ)
    (happrox : |classProductMixture P left right - ν| ≤ α)
    (hτ : τ ≤ η / 8) (hα : α ≤ η / 4) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      if η < |totalTwoHalfCount A B p / populationSize P - ν| then 1 else 0) ≤
        1 / (2 * populationSize P * η ^ 2) := by
  exact twoHalf_inheritedMask_rejection_le A B hn hm η ν hη
    (totalMatchingMean_inherited_margin A B hm left right η τ α ν
      hright0 hright1 hleft hright happrox hτ hα)

theorem selectedTwoHalfMask_rejection_of_windows_le
    (D : Finset C) (A B : ∀ c, Finset (P c))
    (hn : ∀ c ∈ D, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize (fun c : D => P c))
    (left right : C → ℝ) (η τ α ν : ℝ) (hη : 0 < η)
    (hright0 : ∀ c ∈ D, 0 ≤ right c) (hright1 : ∀ c ∈ D, right c ≤ 1)
    (hleft : ∀ c ∈ D, |classDensity A c - left c| ≤ τ)
    (hright : ∀ c ∈ D, |classDensity B c - right c| ≤ τ)
    (happrox : |classProductMixture (fun c : D => P c)
      (fun c => left c) (fun c => right c) - ν| ≤ α)
    (hτ : τ ≤ η / 8) (hα : α ≤ η / 4) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      if η < |selectedTwoHalfCount D A B p /
        populationSize (fun c : D => P c) - ν| then 1 else 0) ≤
      1 / (2 * populationSize (fun c : D => P c) * η ^ 2) := by
  let : ∀ c : D, Nonempty (P c) := fun c =>
    Fintype.card_pos_iff.mp (lt_of_lt_of_le (by decide : 0 < 2) (hn c c.property))
  apply selectedTwoHalfMask_rejection_le D A B hn hm η ν hη
  exact totalMatchingMean_inherited_margin (fun c : D => A c) (fun c : D => B c)
    hm (fun c => left c) (fun c => right c) η τ α ν
    (fun c => hright0 c c.property) (fun c => hright1 c c.property)
    (fun c => hleft c c.property) (fun c => hright c c.property) happrox hτ hα

end ClassMixtures

section CompleteWordStatistics

variable {C : Type*} [Fintype C] [DecidableEq C] {P X Y S T : C → Type*}
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (S c)] [∀ c, DecidableEq (S c)]
  [∀ c, Fintype (T c)] [∀ c, DecidableEq (T c)]

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (P c)] in
theorem classDensity_statisticPositions (w : ∀ c, P c → X c)
    (statistic : ∀ c, X c → S c) (s : ∀ c, S c) (c : C) :
    classDensity (fun c => statisticPositions (w c) (statistic c) (s c)) c =
      empiricalLaw (statistic c ∘ w c) (s c) := by
  rw [classDensity, statisticPositions_card, empiricalLaw]

omit [DecidableEq C] in
theorem totalMatchingMean_statistic_eq [∀ c, Nonempty (P c)]
    (w : ∀ c, P c → X c) (v : ∀ c, P c → Y c)
    (leftStat : ∀ c, X c → S c) (rightStat : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c) (hm : 0 < populationSize P) :
    totalMatchingMean (fun c => statisticPositions (w c) (leftStat c) (s c))
        (fun c => statisticPositions (v c) (rightStat c) (t c)) / populationSize P =
      classProductMixture P
        (fun c => empiricalLaw (leftStat c ∘ w c) (s c))
        (fun c => empiricalLaw (rightStat c ∘ v c) (t c)) := by
  rw [totalMatchingMean_normalized_eq _ _ hm]
  simp only [classProductMixture, classDensity_statisticPositions]

theorem twoHalf_statistic_rejection_of_typeWindows_le [∀ c, Nonempty (P c)]
    (w : ∀ c, P c → X c) (v : ∀ c, P c → Y c)
    (leftStat : ∀ c, X c → S c) (rightStat : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c)
    (hn : ∀ c, 2 ≤ Fintype.card (P c)) (hm : 0 < populationSize P)
    (leftLaw : ∀ c, S c → ℝ) (rightLaw : ∀ c, T c → ℝ)
    (η τ α ν : ℝ) (hη : 0 < η)
    (hright0 : ∀ c, 0 ≤ rightLaw c (t c))
    (hright1 : ∀ c, rightLaw c (t c) ≤ 1)
    (hleft : ∀ c, typeWindow (leftLaw c) τ (leftStat c ∘ w c))
    (hright : ∀ c, typeWindow (rightLaw c) τ (rightStat c ∘ v c))
    (happrox : |classProductMixture P
      (fun c => leftLaw c (s c)) (fun c => rightLaw c (t c)) - ν| ≤ α)
    (hτ : τ ≤ η / 8) (hα : α ≤ η / 4) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      if η < |totalTwoHalfCount
          (fun c => statisticPositions (w c) (leftStat c) (s c))
          (fun c => statisticPositions (v c) (rightStat c) (t c)) p /
          populationSize P - ν| then 1 else 0) ≤
        1 / (2 * populationSize P * η ^ 2) := by
  apply twoHalf_inheritedMask_rejection_of_windows_le _ _ hn hm
    (fun c => leftLaw c (s c)) (fun c => rightLaw c (t c)) η τ α ν hη
    hright0 hright1
  · intro c
    simpa only [classDensity_statisticPositions] using hleft c (s c)
  · intro c
    simpa only [classDensity_statisticPositions] using hright c (t c)
  · exact happrox
  · exact hτ
  · exact hα

theorem selectedTwoHalf_statistic_rejection_of_completeWindows_le
    [∀ c, Fintype (X c)] [∀ c, DecidableEq (X c)]
    [∀ c, Fintype (Y c)] [∀ c, DecidableEq (Y c)]
    (D : Finset C) (w : ∀ c, P c → X c) (v : ∀ c, P c → Y c)
    (leftStat : ∀ c, X c → S c) (rightStat : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c)
    (hn : ∀ c ∈ D, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize (fun c : D => P c))
    (leftLaw : ∀ c, X c → ℝ) (rightLaw : ∀ c, Y c → ℝ)
    (leftε rightε : C → ℝ) (η α ν : ℝ) (hη : 0 < η)
    (hright0 : ∀ c ∈ D, ∀ y, 0 ≤ rightLaw c y)
    (hrightSum : ∀ c ∈ D, ∑ y, rightLaw c y = 1)
    (hleftε : ∀ c ∈ D, 0 ≤ leftε c) (hrightε : ∀ c ∈ D, 0 ≤ rightε c)
    (hleft : ∀ c ∈ D, typeWindow (leftLaw c) (leftε c) (w c))
    (hright : ∀ c ∈ D, typeWindow (rightLaw c) (rightε c) (v c))
    (hleftFactor : ∀ c ∈ D, (Fintype.card (X c) : ℝ) * leftε c ≤ η / 8)
    (hrightFactor : ∀ c ∈ D, (Fintype.card (Y c) : ℝ) * rightε c ≤ η / 8)
    (happrox : |classProductMixture (fun c : D => P c)
      (fun c => pushforwardLaw (leftStat c) (leftLaw c) (s c))
      (fun c => pushforwardLaw (rightStat c) (rightLaw c) (t c)) - ν| ≤ α)
    (hα : α ≤ η / 4) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      if η < |selectedTwoHalfCount D
          (fun c => statisticPositions (w c) (leftStat c) (s c))
          (fun c => statisticPositions (v c) (rightStat c) (t c)) p /
          populationSize (fun c : D => P c) - ν| then 1 else 0) ≤
        1 / (2 * populationSize (fun c : D => P c) * η ^ 2) := by
  apply selectedTwoHalfMask_rejection_of_windows_le D _ _ hn hm
    (fun c => pushforwardLaw (leftStat c) (leftLaw c) (s c))
    (fun c => pushforwardLaw (rightStat c) (rightLaw c) (t c))
    η (η / 8) α ν hη
  · intro c hc
    exact pushforwardLaw_nonneg (rightStat c) (rightLaw c) (hright0 c hc) (t c)
  · intro c hc
    exact pushforwardLaw_le_one (rightStat c) (rightLaw c)
      (hright0 c hc) (hrightSum c hc) (t c)
  · intro c hc
    rw [classDensity_statisticPositions]
    exact (typeWindow_statistic (leftLaw c) (leftε c) (w c) (leftStat c)
      (hleftε c hc) (hleft c hc) (s c)).trans (hleftFactor c hc)
  · intro c hc
    rw [classDensity_statisticPositions]
    exact (typeWindow_statistic (rightLaw c) (rightε c) (v c) (rightStat c)
      (hrightε c hc) (hright c hc) (t c)).trans (hrightFactor c hc)
  · exact happrox
  · exact le_rfl
  · exact hα

end CompleteWordStatistics

end

end MatrixMultiplication.PermutationMatching

end OAI
