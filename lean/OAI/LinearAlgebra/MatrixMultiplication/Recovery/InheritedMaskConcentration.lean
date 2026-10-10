import OAI.LinearAlgebra.MatrixMultiplication.Recovery.PermutationMatchingHalves
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.InheritedMasks
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.OrbitCounting
import Mathlib.Algebra.BigOperators.Field

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators
open Classical

noncomputable section

section ClassProducts

variable {C : Type*} [Fintype C] [DecidableEq C] {P : C → Type*}
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]

abbrev ClassPermutations (P : C → Type*) := ∀ c, Equiv.Perm (P c)

def populationSize (P : C → Type*) [∀ c, Fintype (P c)] : ℝ :=
  ∑ c, (Fintype.card (P c) : ℝ)

def totalMatchingCount (A B : ∀ c, Finset (P c))
    (p : ClassPermutations P) : ℝ :=
  ∑ c, matchingCount (A c) (B c) (p c)

def totalMatchingMean (A B : ∀ c, Finset (P c)) : ℝ :=
  ∑ c, average (matchingCount (A c) (B c))

theorem average_totalMatchingCount (A B : ∀ c, Finset (P c)) :
    average (totalMatchingCount A B) = totalMatchingMean A B := by
  classical
  unfold totalMatchingCount totalMatchingMean
  rw [average_sum]
  apply Finset.sum_congr rfl
  intro c _
  exact average_pi_eval (X := fun c => Equiv.Perm (P c)) c
    (matchingCount (A c) (B c))

omit [DecidableEq C] in
theorem totalMatchingMean_eq [∀ c, Nonempty (P c)]
    (A B : ∀ c, Finset (P c)) :
    totalMatchingMean A B =
      ∑ c, ((A c).card : ℝ) * ((B c).card : ℝ) / (Fintype.card (P c) : ℝ) := by
  classical
  unfold totalMatchingMean
  apply Finset.sum_congr rfl
  intro c _
  exact average_matchingCount (A c) (B c)

theorem totalMatchingCount_variance_le (A B : ∀ c, Finset (P c))
    (hn : ∀ c, 2 ≤ Fintype.card (P c)) :
    average (fun p : ClassPermutations P =>
      (totalMatchingCount A B p - totalMatchingMean A B) ^ 2) ≤
        populationSize P / 8 := by
  classical
  calc
    _ = ∑ c, average (fun p : Equiv.Perm (P c) =>
        (matchingCount (A c) (B c) p - average (matchingCount (A c) (B c))) ^ 2) := by
      simpa only [totalMatchingCount, totalMatchingMean, Finset.sum_sub_distrib]
        using average_pi_sum_centered_sq (fun c => matchingCount (A c) (B c))
    _ ≤ ∑ c, (Fintype.card (P c) : ℝ) / 8 :=
      Finset.sum_le_sum fun c _ => matchingCount_variance_le (A c) (B c) (hn c)
    _ = populationSize P / 8 := by rw [← Finset.sum_div]; rfl

theorem totalMatchingCount_deviation_le (A B : ∀ c, Finset (P c))
    (hn : ∀ c, 2 ≤ Fintype.card (P c)) (δ : ℝ) (hδ : 0 < δ) :
    average (fun p : ClassPermutations P =>
      if δ ≤ |totalMatchingCount A B p - totalMatchingMean A B| then 1 else 0) ≤
        populationSize P / (8 * δ ^ 2) := by
  classical
  have h := (deviation_bound (totalMatchingCount A B) (totalMatchingMean A B) δ hδ).trans
    (totalMatchingCount_variance_le A B hn)
  calc
    _ ≤ (populationSize P / 8) / δ ^ 2 := (le_div_iff₀ (sq_pos_of_pos hδ)).2 h
    _ = _ := by rw [div_div]

theorem normalizedMatchingCount_deviation_le (A B : ∀ c, Finset (P c))
    (hn : ∀ c, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize P) (η : ℝ) (hη : 0 < η) :
    average (fun p : ClassPermutations P =>
      if η / 2 ≤ |totalMatchingCount A B p / populationSize P -
          totalMatchingMean A B / populationSize P| then 1 else 0) ≤
        1 / (2 * populationSize P * η ^ 2) := by
  classical
  have hδ : 0 < populationSize P * η / 2 := by positivity
  calc
    _ ≤ average (fun p : ClassPermutations P =>
        if populationSize P * η / 2 ≤
          |totalMatchingCount A B p - totalMatchingMean A B| then 1 else 0) := by
      apply average_mono
      intro p
      have hi : η / 2 ≤ |totalMatchingCount A B p / populationSize P -
          totalMatchingMean A B / populationSize P| →
          populationSize P * η / 2 ≤
            |totalMatchingCount A B p - totalMatchingMean A B| := by
        intro hp
        rw [← sub_div, abs_div, abs_of_pos hm] at hp
        have hh := (le_div_iff₀ hm).mp hp
        nlinarith
      split_ifs <;> simp_all
    _ ≤ populationSize P / (8 * (populationSize P * η / 2) ^ 2) :=
      totalMatchingCount_deviation_le A B hn _ hδ
    _ = _ := by
      field_simp [ne_of_gt hm, ne_of_gt hη]
      ring

theorem inheritedMask_rejection_le (A B : ∀ c, Finset (P c))
    (hn : ∀ c, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize P) (η ν : ℝ) (hη : 0 < η)
    (hmargin : |totalMatchingMean A B / populationSize P - ν| ≤ η / 2) :
    average (fun p : ClassPermutations P =>
      if η < |totalMatchingCount A B p / populationSize P - ν| then 1 else 0) ≤
        1 / (2 * populationSize P * η ^ 2) := by
  classical
  refine le_trans (average_mono ?_) (normalizedMatchingCount_deviation_le A B hn hm η hη)
  intro p
  have hi : η < |totalMatchingCount A B p / populationSize P - ν| →
      η / 2 ≤ |totalMatchingCount A B p / populationSize P -
        totalMatchingMean A B / populationSize P| := by
    intro hp
    have ht : |totalMatchingCount A B p / populationSize P - ν| ≤
        |totalMatchingCount A B p / populationSize P -
          totalMatchingMean A B / populationSize P| +
        |totalMatchingMean A B / populationSize P - ν| := by
      simpa only [sub_add_sub_cancel] using abs_add_le
        (totalMatchingCount A B p / populationSize P - totalMatchingMean A B / populationSize P)
        (totalMatchingMean A B / populationSize P - ν)
    linarith
  split_ifs <;> simp_all

theorem finite_inheritedMask_rejection_le {I : Type*} [Fintype I]
    (A B : I → ∀ c, Finset (P c))
    (hn : ∀ c, 2 ≤ Fintype.card (P c)) (hm : 0 < populationSize P)
    (η ν : I → ℝ) (hη : ∀ i, 0 < η i)
    (hmargin : ∀ i, |totalMatchingMean (A i) (B i) / populationSize P - ν i| ≤ η i / 2) :
    average (fun p : ClassPermutations P =>
      if ∃ i, η i < |totalMatchingCount (A i) (B i) p / populationSize P - ν i|
        then 1 else 0) ≤ ∑ i, 1 / (2 * populationSize P * (η i) ^ 2) := by
  classical
  refine le_trans (average_indicator_exists_le_sum _) ?_
  exact Finset.sum_le_sum fun i _ =>
    inheritedMask_rejection_le (A i) (B i) hn hm (η i) (ν i) (hη i) (hmargin i)

theorem pushforward_sum_rejection_le {I : Type*} [Fintype I]
    (A B : I → ∀ c, Finset (P c))
    (hn : ∀ c, 2 ≤ Fintype.card (P c)) (hm : 0 < populationSize P)
    (η : ℝ) (ν : I → ℝ) (hη : 0 < η)
    (hmargin : ∀ i, |totalMatchingMean (A i) (B i) / populationSize P - ν i| ≤
      (η / Fintype.card I) / 2) :
    average (fun p : ClassPermutations P =>
      if η < |(∑ i, totalMatchingCount (A i) (B i) p / populationSize P) - ∑ i, ν i|
        then 1 else 0) ≤
          ∑ _i : I, 1 / (2 * populationSize P * (η / Fintype.card I) ^ 2) := by
  classical
  by_cases hIcard : Fintype.card I = 0
  · have : IsEmpty I := Fintype.card_eq_zero_iff.mp hIcard
    simp [not_lt.mpr (le_of_lt hη)]
  have : Nonempty I := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hIcard)
  have hcard : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos
  have htol : 0 < η / (Fintype.card I : ℝ) := div_pos hη hcard
  refine le_trans (average_mono ?_)
    (finite_inheritedMask_rejection_le A B hn hm (fun _ => η / Fintype.card I)
      ν (fun _ => htol) hmargin)
  intro p
  have hi : η < |(∑ i, totalMatchingCount (A i) (B i) p / populationSize P) -
      ∑ i, ν i| →
      ∃ i, η / Fintype.card I <
        |totalMatchingCount (A i) (B i) p / populationSize P - ν i| := by
    intro hp
    by_contra h
    push Not at h
    have he : |(∑ i, totalMatchingCount (A i) (B i) p / populationSize P) -
        ∑ i, ν i| ≤ η := by
      rw [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ i, |totalMatchingCount (A i) (B i) p / populationSize P - ν i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : I, η / Fintype.card I := Finset.sum_le_sum fun i _ => h i
        _ = η := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp [ne_of_gt hcard]
    linarith
  split_ifs <;> simp_all

def totalTwoHalfCount (A B : ∀ c, Finset (P c))
    (p : ClassPermutations P × ClassPermutations P) : ℝ :=
  ∑ c, twoHalfCount (A c) (B c) (p.1 c) (p.2 c)

theorem average_totalTwoHalfCount_test (A B : ∀ c, Finset (P c)) (f : ℝ → ℝ) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      f (totalTwoHalfCount A B p)) =
        average (fun p : ClassPermutations P => f (totalMatchingCount A B p)) := by
  calc
    _ = average (fun p : ClassPermutations P × ClassPermutations P =>
        f (totalMatchingCount A B (relativeFamily P p.1 p.2))) := by
      apply average_congr
      intro p
      exact congrArg f (sum_twoHalfCount_eq_matchingCount P A B p.1 p.2)
    _ = _ := average_relativeFamily P (fun p => f (totalMatchingCount A B p))

theorem average_totalTwoHalfCounts_test {I : Type*}
    (A B : I → ∀ c, Finset (P c)) (f : (I → ℝ) → ℝ) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      f (fun i => totalTwoHalfCount (A i) (B i) p)) =
        average (fun p : ClassPermutations P =>
          f (fun i => totalMatchingCount (A i) (B i) p)) := by
  calc
    _ = average (fun p : ClassPermutations P × ClassPermutations P =>
        f (fun i => totalMatchingCount (A i) (B i) (relativeFamily P p.1 p.2))) := by
      apply average_congr
      intro p
      apply congrArg f
      funext i
      exact sum_twoHalfCount_eq_matchingCount P (A i) (B i) p.1 p.2
    _ = _ := average_relativeFamily P
      (fun p => f (fun i => totalMatchingCount (A i) (B i) p))

theorem twoHalf_pushforward_sum_rejection_le {I : Type*} [Fintype I]
    (A B : I → ∀ c, Finset (P c))
    (hn : ∀ c, 2 ≤ Fintype.card (P c)) (hm : 0 < populationSize P)
    (η : ℝ) (ν : I → ℝ) (hη : 0 < η)
    (hmargin : ∀ i, |totalMatchingMean (A i) (B i) / populationSize P - ν i| ≤
      (η / Fintype.card I) / 2) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      if η < |(∑ i, totalTwoHalfCount (A i) (B i) p / populationSize P) - ∑ i, ν i|
        then 1 else 0) ≤
          ∑ _i : I, 1 / (2 * populationSize P * (η / Fintype.card I) ^ 2) := by
  classical
  rw [average_totalTwoHalfCounts_test A B
    (fun k => if η < |(∑ i, k i / populationSize P) - ∑ i, ν i| then 1 else 0)]
  exact pushforward_sum_rejection_le A B hn hm η ν hη hmargin

theorem twoHalf_inheritedMask_rejection_le (A B : ∀ c, Finset (P c))
    (hn : ∀ c, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize P) (η ν : ℝ) (hη : 0 < η)
    (hmargin : |totalMatchingMean A B / populationSize P - ν| ≤ η / 2) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      if η < |totalTwoHalfCount A B p / populationSize P - ν| then 1 else 0) ≤
        1 / (2 * populationSize P * η ^ 2) := by
  classical
  rw [average_totalTwoHalfCount_test A B
    (fun k => if η < |k / populationSize P - ν| then 1 else 0)]
  exact inheritedMask_rejection_le A B hn hm η ν hη hmargin

def selectedTwoHalfCount (D : Finset C) (A B : ∀ c, Finset (P c))
    (p : ClassPermutations P × ClassPermutations P) : ℝ :=
  totalTwoHalfCount (fun c : D => A c) (fun c : D => B c)
    ((fun c => p.1 c), (fun c => p.2 c))

theorem selectedTwoHalfMask_rejection_le (D : Finset C) (A B : ∀ c, Finset (P c))
    (hn : ∀ c ∈ D, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize (fun c : D => P c)) (η ν : ℝ) (hη : 0 < η)
    (hmargin : |totalMatchingMean (fun c : D => A c) (fun c : D => B c) /
      populationSize (fun c : D => P c) - ν| ≤ η / 2) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      if η < |selectedTwoHalfCount D A B p / populationSize (fun c : D => P c) - ν|
        then 1 else 0) ≤ 1 / (2 * populationSize (fun c : D => P c) * η ^ 2) := by
  classical
  have havg := average_prod_pi_restrict (X := fun c => Equiv.Perm (P c)) D
    (fun p : ClassPermutations (fun c : D => P c) ×
        ClassPermutations (fun c : D => P c) =>
      if η < |totalTwoHalfCount (fun c : D => A c) (fun c : D => B c) p /
        populationSize (fun c : D => P c) - ν| then (1 : ℝ) else 0)
  change average (fun p : ClassPermutations P × ClassPermutations P =>
      if η < |totalTwoHalfCount (fun c : D => A c) (fun c : D => B c)
        ((fun c => p.1 c), (fun c => p.2 c)) /
        populationSize (fun c : D => P c) - ν| then 1 else 0) ≤ _
  rw [havg]
  exact twoHalf_inheritedMask_rejection_le (P := fun c : D => P c)
    (fun c : D => A c) (fun c : D => B c)
    (fun c : D => hn c c.property) hm η ν hη hmargin

theorem finite_selectedTwoHalfMask_rejection_le {I : Type*} [Fintype I]
    (D : I → Finset C) (A B : I → ∀ c, Finset (P c))
    (hn : ∀ i c, c ∈ D i → 2 ≤ Fintype.card (P c))
    (hm : ∀ i, 0 < populationSize (fun c : D i => P c))
    (η ν : I → ℝ) (hη : ∀ i, 0 < η i)
    (hmargin : ∀ i,
      |totalMatchingMean (fun c : D i => A i c) (fun c : D i => B i c) /
        populationSize (fun c : D i => P c) - ν i| ≤ η i / 2) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      if ∃ i, η i < |selectedTwoHalfCount (D i) (A i) (B i) p /
        populationSize (fun c : D i => P c) - ν i| then 1 else 0) ≤
      ∑ i, 1 / (2 * populationSize (fun c : D i => P c) * (η i) ^ 2) := by
  classical
  refine le_trans (average_indicator_exists_le_sum _) ?_
  exact Finset.sum_le_sum fun i _ => selectedTwoHalfMask_rejection_le
    (D i) (A i) (B i) (hn i) (hm i) (η i) (ν i) (hη i) (hmargin i)

theorem inverse_linear_mask_constant {I : Type*} [Fintype I]
    (mass η : I → ℝ) (N : ℝ) :
    (∑ i, 1 / (2 * (mass i * N) * (η i) ^ 2)) =
      (∑ i, 1 / (2 * mass i * (η i) ^ 2)) / N := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [div_div]
  congr 1
  ring

theorem finite_selectedTwoHalfMask_inverse_linear {I : Type*} [Fintype I]
    (D : I → Finset C) (A B : I → ∀ c, Finset (P c))
    (hn : ∀ i c, c ∈ D i → 2 ≤ Fintype.card (P c))
    (mass η ν : I → ℝ) (N : ℝ) (hN : 0 < N)
    (hmass : ∀ i, 0 < mass i) (hη : ∀ i, 0 < η i)
    (hsize : ∀ i, populationSize (fun c : D i => P c) = mass i * N)
    (hmargin : ∀ i,
      |totalMatchingMean (fun c : D i => A i c) (fun c : D i => B i c) /
        populationSize (fun c : D i => P c) - ν i| ≤ η i / 2) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      if ∃ i, η i < |selectedTwoHalfCount (D i) (A i) (B i) p /
        populationSize (fun c : D i => P c) - ν i| then 1 else 0) ≤
      (∑ i, 1 / (2 * mass i * (η i) ^ 2)) / N := by
  have hm (i : I) : 0 < populationSize (fun c : D i => P c) := by
    rw [hsize]
    exact mul_pos (hmass i) hN
  have h := finite_selectedTwoHalfMask_rejection_le D A B hn hm η ν hη hmargin
  simpa only [hsize, inverse_linear_mask_constant] using h

end ClassProducts

section CompleteSymbols

variable {P A S : Type*} [Fintype P] [DecidableEq P] [DecidableEq S]

omit [DecidableEq P] in
theorem statisticPositions_card [Fintype S]
    (w : P → A) (statistic : A → S) (s : S) :
    (statisticPositions w statistic s).card =
      MatrixMultiplication.Foundation.wordPopulation (statistic ∘ w) s := by
  unfold statisticPositions MatrixMultiplication.Foundation.wordPopulation
  rw [Fintype.card_subtype]
  apply congrArg Finset.card
  ext i
  simp

end CompleteSymbols

section OrbitFractions

variable {G X : Type*} [Group G] [MulAction G X] [Fintype G] [DecidableEq X]

theorem average_bad_shift_eq_orbit_fraction (x : X) (bad : X → Prop)
    [DecidablePred bad] :
    average (fun g : G => if bad (g • x) then 1 else 0) =
      (((OrbitCounting.orbitSet (G := G) x).filter bad).card : ℝ) /
        (OrbitCounting.orbitSet (G := G) x).card := by
  rw [average_indicator_eq]
  exact OrbitCounting.bad_shift_fraction x bad

end OrbitFractions

end

end MatrixMultiplication.PermutationMatching

end OAI
