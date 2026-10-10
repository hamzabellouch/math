import OAI.LinearAlgebra.MatrixMultiplication.Recovery.InheritedMaskMargins
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.CompleteWordPair
import Mathlib.Algebra.Group.Equiv.Basic

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators
open MatrixMultiplication.InheritedMasks
open Classical

noncomputable section

variable {C : Type*} {P X Y : C → Type*}
variable [Fintype C] [DecidableEq C]
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
variable {S T : C → Type*}

def wordPairLeftPositions (w : CompleteWordPair P X Y)
    (sl : ∀ c, X c → S c) (s : ∀ c, S c) : ∀ c, Finset (P c) :=
  fun c => statisticPositions (w.left c) (sl c) (s c)

def wordPairRightPositions (w : CompleteWordPair P X Y)
    (sr : ∀ c, Y c → T c) (t : ∀ c, T c) : ∀ c, Finset (P c) :=
  fun c => statisticPositions (w.right c) (sr c) (t c)

def wordPairCount (w : CompleteWordPair P X Y)
    (sl : ∀ c, X c → S c) (sr : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c) : ℝ :=
  ∑ c, ∑ i : P c,
    if sl c (w.left c i) = s c ∧ sr c (w.right c i) = t c then 1 else 0

omit [DecidableEq C] in
theorem wordPairCount_smul (w : CompleteWordPair P X Y)
    (sl : ∀ c, X c → S c) (sr : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c) (g : HalfClassPermutations P) :
    wordPairCount (g • w) sl sr s t =
      totalTwoHalfCount (wordPairLeftPositions w sl s)
        (wordPairRightPositions w sr t) g⁻¹ := by
  unfold wordPairCount totalTwoHalfCount wordPairLeftPositions wordPairRightPositions
  apply Finset.sum_congr rfl
  intro c _
  rw [twoHalfCount_statisticPositions]
  rfl

theorem average_wordPairCount_shift (w : CompleteWordPair P X Y)
    (sl : ∀ c, X c → S c) (sr : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c) (f : ℝ → ℝ) :
    average (fun g : HalfClassPermutations P => f (wordPairCount (g • w) sl sr s t)) =
      average (fun g : HalfClassPermutations P =>
        f (totalTwoHalfCount (wordPairLeftPositions w sl s)
          (wordPairRightPositions w sr t) g)) := by
  simp_rw [wordPairCount_smul]
  exact average_equiv (Equiv.inv (HalfClassPermutations P))
    (fun g => f (totalTwoHalfCount (wordPairLeftPositions w sl s)
      (wordPairRightPositions w sr t) g))

def wordPairMaskBad (sl : ∀ c, X c → S c) (sr : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c) (η ν : ℝ)
    (w : CompleteWordPair P X Y) : Prop :=
  η < |wordPairCount w sl sr s t / populationSize P - ν|

theorem wordPair_orbit_fraction_eq (w : CompleteWordPair P X Y)
    (sl : ∀ c, X c → S c) (sr : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c) (η ν : ℝ) :
    (((OrbitCounting.orbitSet (G := HalfClassPermutations P) w).filter
        (wordPairMaskBad sl sr s t η ν)).card : ℝ) /
      (OrbitCounting.orbitSet (G := HalfClassPermutations P) w).card =
        average (fun g : HalfClassPermutations P =>
          if η < |totalTwoHalfCount (wordPairLeftPositions w sl s)
              (wordPairRightPositions w sr t) g / populationSize P - ν|
            then 1 else 0) := by
  rw [← average_bad_shift_eq_orbit_fraction]
  exact average_wordPairCount_shift w sl sr s t
    (fun k => if η < |k / populationSize P - ν| then 1 else 0)

theorem wordPair_orbit_rejection_le (w : CompleteWordPair P X Y)
    (sl : ∀ c, X c → S c) (sr : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c)
    (hn : ∀ c, 2 ≤ Fintype.card (P c)) (hm : 0 < populationSize P)
    (η ν : ℝ) (hη : 0 < η)
    (hmargin : |totalMatchingMean (wordPairLeftPositions w sl s)
        (wordPairRightPositions w sr t) / populationSize P - ν| ≤ η / 2) :
    (((OrbitCounting.orbitSet (G := HalfClassPermutations P) w).filter
        (wordPairMaskBad sl sr s t η ν)).card : ℝ) /
      (OrbitCounting.orbitSet (G := HalfClassPermutations P) w).card ≤
        1 / (2 * populationSize P * η ^ 2) := by
  rw [wordPair_orbit_fraction_eq]
  exact twoHalf_inheritedMask_rejection_le _ _ hn hm η ν hη hmargin

theorem wordPair_orbit_rejection_of_windows_le [∀ c, Nonempty (P c)]
    (w : CompleteWordPair P X Y)
    (sl : ∀ c, X c → S c) (sr : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c)
    (hn : ∀ c, 2 ≤ Fintype.card (P c)) (hm : 0 < populationSize P)
    (left right : C → ℝ) (η τ α ν : ℝ) (hη : 0 < η)
    (hright0 : ∀ c, 0 ≤ right c) (hright1 : ∀ c, right c ≤ 1)
    (hleft : ∀ c, |classDensity (wordPairLeftPositions w sl s) c - left c| ≤ τ)
    (hright : ∀ c, |classDensity (wordPairRightPositions w sr t) c - right c| ≤ τ)
    (happrox : |classProductMixture P left right - ν| ≤ α)
    (hτ : τ ≤ η / 8) (hα : α ≤ η / 4) :
    (((OrbitCounting.orbitSet (G := HalfClassPermutations P) w).filter
        (wordPairMaskBad sl sr s t η ν)).card : ℝ) /
      (OrbitCounting.orbitSet (G := HalfClassPermutations P) w).card ≤
        1 / (2 * populationSize P * η ^ 2) := by
  exact wordPair_orbit_rejection_le w sl sr s t hn hm η ν hη
    (totalMatchingMean_inherited_margin _ _ hm left right η τ α ν
      hright0 hright1 hleft hright happrox hτ hα)

def selectedWordPairCount (D : Finset C) (w : CompleteWordPair P X Y)
    (sl : ∀ c, X c → S c) (sr : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c) : ℝ :=
  ∑ c : D, ∑ i : P c,
    if sl c (w.left c i) = s c ∧ sr c (w.right c i) = t c then 1 else 0

omit [Fintype C] [DecidableEq C] in
theorem selectedWordPairCount_smul (D : Finset C) (w : CompleteWordPair P X Y)
    (sl : ∀ c, X c → S c) (sr : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c) (g : HalfClassPermutations P) :
    selectedWordPairCount D (g • w) sl sr s t =
      selectedTwoHalfCount D (wordPairLeftPositions w sl s)
        (wordPairRightPositions w sr t) g⁻¹ := by
  unfold selectedWordPairCount selectedTwoHalfCount totalTwoHalfCount
    wordPairLeftPositions wordPairRightPositions
  apply Finset.sum_congr rfl
  intro c _
  rw [twoHalfCount_statisticPositions]
  rfl

theorem average_selectedWordPairCount_shift (D : Finset C)
    (w : CompleteWordPair P X Y)
    (sl : ∀ c, X c → S c) (sr : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c) (f : ℝ → ℝ) :
    average (fun g : HalfClassPermutations P =>
      f (selectedWordPairCount D (g • w) sl sr s t)) =
      average (fun g : HalfClassPermutations P =>
        f (selectedTwoHalfCount D (wordPairLeftPositions w sl s)
          (wordPairRightPositions w sr t) g)) := by
  simp_rw [selectedWordPairCount_smul]
  exact average_equiv (Equiv.inv (HalfClassPermutations P))
    (fun g => f (selectedTwoHalfCount D (wordPairLeftPositions w sl s)
      (wordPairRightPositions w sr t) g))

def selectedWordPairMaskBad (D : Finset C)
    (sl : ∀ c, X c → S c) (sr : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c) (η ν : ℝ)
    (w : CompleteWordPair P X Y) : Prop :=
  η < |selectedWordPairCount D w sl sr s t /
    populationSize (fun c : D => P c) - ν|

theorem selectedWordPair_orbit_fraction_eq (D : Finset C)
    (w : CompleteWordPair P X Y)
    (sl : ∀ c, X c → S c) (sr : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c) (η ν : ℝ) :
    (((OrbitCounting.orbitSet (G := HalfClassPermutations P) w).filter
        (selectedWordPairMaskBad D sl sr s t η ν)).card : ℝ) /
      (OrbitCounting.orbitSet (G := HalfClassPermutations P) w).card =
        average (fun g : HalfClassPermutations P =>
          if η < |selectedTwoHalfCount D (wordPairLeftPositions w sl s)
              (wordPairRightPositions w sr t) g /
                populationSize (fun c : D => P c) - ν| then 1 else 0) := by
  rw [← average_bad_shift_eq_orbit_fraction]
  exact average_selectedWordPairCount_shift D w sl sr s t
    (fun k => if η < |k / populationSize (fun c : D => P c) - ν| then 1 else 0)

theorem selectedWordPair_orbit_rejection_le (D : Finset C)
    (w : CompleteWordPair P X Y)
    (sl : ∀ c, X c → S c) (sr : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c)
    (hn : ∀ c ∈ D, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize (fun c : D => P c)) (η ν : ℝ) (hη : 0 < η)
    (hmargin : |totalMatchingMean
        (fun c : D => wordPairLeftPositions w sl s c)
        (fun c : D => wordPairRightPositions w sr t c) /
          populationSize (fun c : D => P c) - ν| ≤ η / 2) :
    (((OrbitCounting.orbitSet (G := HalfClassPermutations P) w).filter
        (selectedWordPairMaskBad D sl sr s t η ν)).card : ℝ) /
      (OrbitCounting.orbitSet (G := HalfClassPermutations P) w).card ≤
        1 / (2 * populationSize (fun c : D => P c) * η ^ 2) := by
  rw [selectedWordPair_orbit_fraction_eq]
  exact selectedTwoHalfMask_rejection_le D _ _ hn hm η ν hη hmargin

theorem selectedWordPair_orbit_rejection_of_windows_le (D : Finset C)
    (w : CompleteWordPair P X Y)
    (sl : ∀ c, X c → S c) (sr : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c)
    (hn : ∀ c ∈ D, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize (fun c : D => P c))
    (left right : C → ℝ) (η τ α ν : ℝ) (hη : 0 < η)
    (hright0 : ∀ c ∈ D, 0 ≤ right c) (hright1 : ∀ c ∈ D, right c ≤ 1)
    (hleft : ∀ c ∈ D, |classDensity (wordPairLeftPositions w sl s) c - left c| ≤ τ)
    (hright : ∀ c ∈ D, |classDensity (wordPairRightPositions w sr t) c - right c| ≤ τ)
    (happrox : |classProductMixture (fun c : D => P c)
      (fun c => left c) (fun c => right c) - ν| ≤ α)
    (hτ : τ ≤ η / 8) (hα : α ≤ η / 4) :
    (((OrbitCounting.orbitSet (G := HalfClassPermutations P) w).filter
        (selectedWordPairMaskBad D sl sr s t η ν)).card : ℝ) /
      (OrbitCounting.orbitSet (G := HalfClassPermutations P) w).card ≤
        1 / (2 * populationSize (fun c : D => P c) * η ^ 2) := by
  rw [selectedWordPair_orbit_fraction_eq]
  exact selectedTwoHalfMask_rejection_of_windows_le D _ _ hn hm left right
    η τ α ν hη hright0 hright1 hleft hright happrox hτ hα

theorem selectedWordPair_orbit_rejection_of_completeWindows_le
    [∀ c, Fintype (X c)] [∀ c, DecidableEq (X c)]
    [∀ c, Fintype (Y c)] [∀ c, DecidableEq (Y c)]
    [∀ c, Fintype (S c)] [∀ c, DecidableEq (S c)]
    [∀ c, Fintype (T c)] [∀ c, DecidableEq (T c)]
    (D : Finset C) (w : CompleteWordPair P X Y)
    (sl : ∀ c, X c → S c) (sr : ∀ c, Y c → T c)
    (s : ∀ c, S c) (t : ∀ c, T c)
    (hn : ∀ c ∈ D, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize (fun c : D => P c))
    (leftLaw : ∀ c, X c → ℝ) (rightLaw : ∀ c, Y c → ℝ)
    (leftε rightε : C → ℝ) (η α ν : ℝ) (hη : 0 < η)
    (hright0 : ∀ c ∈ D, ∀ y, 0 ≤ rightLaw c y)
    (hrightSum : ∀ c ∈ D, ∑ y, rightLaw c y = 1)
    (hleftε : ∀ c ∈ D, 0 ≤ leftε c) (hrightε : ∀ c ∈ D, 0 ≤ rightε c)
    (hleft : ∀ c ∈ D, typeWindow (leftLaw c) (leftε c) (w.left c))
    (hright : ∀ c ∈ D, typeWindow (rightLaw c) (rightε c) (w.right c))
    (hleftFactor : ∀ c ∈ D, (Fintype.card (X c) : ℝ) * leftε c ≤ η / 8)
    (hrightFactor : ∀ c ∈ D, (Fintype.card (Y c) : ℝ) * rightε c ≤ η / 8)
    (happrox : |classProductMixture (fun c : D => P c)
      (fun c => pushforwardLaw (sl c) (leftLaw c) (s c))
      (fun c => pushforwardLaw (sr c) (rightLaw c) (t c)) - ν| ≤ α)
    (hα : α ≤ η / 4) :
    (((OrbitCounting.orbitSet (G := HalfClassPermutations P) w).filter
        (selectedWordPairMaskBad D sl sr s t η ν)).card : ℝ) /
      (OrbitCounting.orbitSet (G := HalfClassPermutations P) w).card ≤
        1 / (2 * populationSize (fun c : D => P c) * η ^ 2) := by
  rw [selectedWordPair_orbit_fraction_eq]
  exact selectedTwoHalf_statistic_rejection_of_completeWindows_le D w.left w.right
    sl sr s t hn hm leftLaw rightLaw leftε rightε η α ν hη hright0 hrightSum
    hleftε hrightε hleft hright hleftFactor hrightFactor happrox hα

section FiniteMasks

variable {I : Type*} [Fintype I] {SL SR : I → C → Type*}

theorem finite_selectedWordPair_sum_orbit_fraction_le
    (D : I → Finset C) (w : CompleteWordPair P X Y)
    (sl : ∀ i c, X c → SL i c) (sr : ∀ i c, Y c → SR i c)
    (s : ∀ i c, SL i c) (t : ∀ i c, SR i c) (η : ℝ) (ν : I → ℝ)
    (hη : 0 ≤ η) :
    (((OrbitCounting.orbitSet (G := HalfClassPermutations P) w).filter
        (fun v => η < |(∑ i, selectedWordPairCount (D i) v
          (sl i) (sr i) (s i) (t i) / populationSize (fun c : D i => P c)) -
            ∑ i, ν i|)).card : ℝ) /
      (OrbitCounting.orbitSet (G := HalfClassPermutations P) w).card ≤
    (((OrbitCounting.orbitSet (G := HalfClassPermutations P) w).filter
        (fun v => ∃ i, selectedWordPairMaskBad (D i) (sl i) (sr i)
          (s i) (t i) (η / Fintype.card I) (ν i) v)).card : ℝ) /
      (OrbitCounting.orbitSet (G := HalfClassPermutations P) w).card := by
  by_cases hI : Fintype.card I = 0
  · have : IsEmpty I := Fintype.card_eq_zero_iff.mp hI
    simp [not_lt_of_ge hη]
  have : Nonempty I := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hI)
  have hcard : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast (Fintype.card_pos (α := I))
  let z (v : CompleteWordPair P X Y) (i : I) : ℝ :=
    selectedWordPairCount (D i) v (sl i) (sr i) (s i) (t i) /
      populationSize (fun c : D i => P c)
  let R := OrbitCounting.orbitSet (G := HalfClassPermutations P) w
  let sumBad (v : CompleteWordPair P X Y) : Prop :=
    η < |(∑ i, z v i) - ∑ i, ν i|
  let unionBad (v : CompleteWordPair P X Y) : Prop :=
    ∃ i, selectedWordPairMaskBad (D i) (sl i) (sr i)
      (s i) (t i) (η / Fintype.card I) (ν i) v
  have hEvent (v) (hv : sumBad v) : unionBad v := by
    change ∃ i, η / Fintype.card I < |z v i - ν i|
    change η < |(∑ i, z v i) - ∑ i, ν i| at hv
    by_contra h
    push Not at h
    have he : |(∑ i, z v i) - ∑ i, ν i| ≤ η := by
      rw [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ i, |z v i - ν i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : I, η / Fintype.card I := Finset.sum_le_sum fun i _ => h i
        _ = η := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp [ne_of_gt hcard]
    linarith
  have hsub : R.filter sumBad ⊆ R.filter unionBad :=
    Finset.monotone_filter_right R (fun v _ => hEvent v)
  have hcards : ((R.filter sumBad).card : ℝ) ≤ (R.filter unionBad).card := by
    exact_mod_cast Finset.card_le_card hsub
  exact div_le_div_of_nonneg_right hcards (Nat.cast_nonneg R.card)

theorem finite_selectedWordPair_orbit_rejection_of_windows_le
    (D : I → Finset C) (w : CompleteWordPair P X Y)
    (sl : ∀ i c, X c → SL i c) (sr : ∀ i c, Y c → SR i c)
    (s : ∀ i c, SL i c) (t : ∀ i c, SR i c)
    (hn : ∀ i c, c ∈ D i → 2 ≤ Fintype.card (P c))
    (hm : ∀ i, 0 < populationSize (fun c : D i => P c))
    (left right : I → C → ℝ) (η τ α ν : I → ℝ) (hη : ∀ i, 0 < η i)
    (hright0 : ∀ i c, c ∈ D i → 0 ≤ right i c)
    (hright1 : ∀ i c, c ∈ D i → right i c ≤ 1)
    (hleft : ∀ i c, c ∈ D i →
      |classDensity (wordPairLeftPositions w (sl i) (s i)) c - left i c| ≤ τ i)
    (hright : ∀ i c, c ∈ D i →
      |classDensity (wordPairRightPositions w (sr i) (t i)) c - right i c| ≤ τ i)
    (happrox : ∀ i, |classProductMixture (fun c : D i => P c)
      (fun c => left i c) (fun c => right i c) - ν i| ≤ α i)
    (hτ : ∀ i, τ i ≤ η i / 8) (hα : ∀ i, α i ≤ η i / 4) :
    (((OrbitCounting.orbitSet (G := HalfClassPermutations P) w).filter
        (fun v => ∃ i, selectedWordPairMaskBad (D i) (sl i) (sr i)
          (s i) (t i) (η i) (ν i) v)).card : ℝ) /
      (OrbitCounting.orbitSet (G := HalfClassPermutations P) w).card ≤
        ∑ i, 1 / (2 * populationSize (fun c : D i => P c) * (η i) ^ 2) := by
  rw [← average_bad_shift_eq_orbit_fraction]
  refine le_trans (average_indicator_exists_le_sum _) ?_
  apply Finset.sum_le_sum
  intro i _
  change average (fun g : HalfClassPermutations P =>
    if η i < |selectedWordPairCount (D i) (g • w) (sl i) (sr i) (s i) (t i) /
      populationSize (fun c : D i => P c) - ν i| then 1 else 0) ≤ _
  rw [average_selectedWordPairCount_shift (D i) w (sl i) (sr i) (s i) (t i)
    (fun k => if η i < |k / populationSize (fun c : D i => P c) - ν i|
      then 1 else 0)]
  exact selectedTwoHalfMask_rejection_of_windows_le (D i) _ _ (hn i) (hm i)
    (left i) (right i) (η i) (τ i) (α i) (ν i) (hη i)
    (hright0 i) (hright1 i) (hleft i) (hright i) (happrox i) (hτ i) (hα i)

theorem finite_selectedWordPair_orbit_inverse_linear_of_windows
    (D : I → Finset C) (w : CompleteWordPair P X Y)
    (sl : ∀ i c, X c → SL i c) (sr : ∀ i c, Y c → SR i c)
    (s : ∀ i c, SL i c) (t : ∀ i c, SR i c)
    (hn : ∀ i c, c ∈ D i → 2 ≤ Fintype.card (P c))
    (mass : I → ℝ) (N : ℝ) (hN : 0 < N) (hmass : ∀ i, 0 < mass i)
    (hsize : ∀ i, populationSize (fun c : D i => P c) = mass i * N)
    (left right : I → C → ℝ) (η τ α ν : I → ℝ) (hη : ∀ i, 0 < η i)
    (hright0 : ∀ i c, c ∈ D i → 0 ≤ right i c)
    (hright1 : ∀ i c, c ∈ D i → right i c ≤ 1)
    (hleft : ∀ i c, c ∈ D i →
      |classDensity (wordPairLeftPositions w (sl i) (s i)) c - left i c| ≤ τ i)
    (hright : ∀ i c, c ∈ D i →
      |classDensity (wordPairRightPositions w (sr i) (t i)) c - right i c| ≤ τ i)
    (happrox : ∀ i, |classProductMixture (fun c : D i => P c)
      (fun c => left i c) (fun c => right i c) - ν i| ≤ α i)
    (hτ : ∀ i, τ i ≤ η i / 8) (hα : ∀ i, α i ≤ η i / 4) :
    (((OrbitCounting.orbitSet (G := HalfClassPermutations P) w).filter
        (fun v => ∃ i, selectedWordPairMaskBad (D i) (sl i) (sr i)
          (s i) (t i) (η i) (ν i) v)).card : ℝ) /
      (OrbitCounting.orbitSet (G := HalfClassPermutations P) w).card ≤
        (∑ i, 1 / (2 * mass i * (η i) ^ 2)) / N := by
  have hm (i : I) : 0 < populationSize (fun c : D i => P c) := by
    rw [hsize]
    exact mul_pos (hmass i) hN
  have h := finite_selectedWordPair_orbit_rejection_of_windows_le D w sl sr s t hn hm
    left right η τ α ν hη hright0 hright1 hleft hright happrox hτ hα
  simpa only [hsize, inverse_linear_mask_constant] using h

end FiniteMasks

end

end MatrixMultiplication.PermutationMatching

end OAI
