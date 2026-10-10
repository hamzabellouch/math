import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.JointCanonicalMixed
import OAI.LinearAlgebra.MatrixFields.Histories.GroupOrbitCount

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
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
    Finset.monotone_filter_right R (fun value _ => hEvent value)
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





noncomputable section

namespace MatrixMultiplication.AllFieldHistoryMasks

open AllFieldHistory AllFieldHistoryChildLaws AllFieldHistorySupport
open JointCanonicalization InheritedMasks PermutationMatching HistorySymmetry
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

abbrev Classes (K tick : ℕ) := Active K tick × JointPopulation.Shape

abbrev Positions (allocation : Allocation) (m : ℕ) (c : Classes K tick) :=
  Fin (activeCounts allocation m c.1 c.2)

abbrev Letters (c : Classes K tick) := Fin (activeHalfLength c.1) → Fin 7

abbrev Words (allocation : Allocation) (m : ℕ) :=
  CompleteWordPair (Positions (K := K) (tick := tick) allocation m) Letters Letters

noncomputable instance permutationsFintype (allocation : Allocation) (m : ℕ) :
    Fintype (HalfClassPermutations (Positions (K := K) (tick := tick) allocation m)) := by
  letI : DecidableEq (Classes K tick) := Classical.decEq _
  letI : ∀ c : Classes K tick, DecidableEq (Positions allocation m c) :=
    fun _ => Classical.decEq _
  letI : Fintype (Classes K tick) := inferInstance
  letI : ∀ c : Classes K tick, Fintype (Equiv.Perm (Positions allocation m c)) :=
    fun c => Equiv.instFintype
  letI : Fintype ((c : Classes K tick) → Equiv.Perm (Positions allocation m c)) :=
    Pi.instFintype
  change Fintype (((c : Classes K tick) → Equiv.Perm (Positions allocation m c)) ×
    ((c : Classes K tick) → Equiv.Perm (Positions allocation m c)))
  infer_instance

abbrev SymbolChoice (K tick : ℕ) := ∀ h : Active K tick, Statistic h

abbrev MaskIndex (K tick : ℕ) := Active K tick × SymbolChoice K tick × SymbolChoice K tick

def testedClasses (allocation : Allocation) (i : MaskIndex K tick) : Finset (Classes K tick) :=
  positiveClasses allocation i.1

def pairWidth (ε : ℝ) (h : Active K tick) : ℝ := ε / 16 ^ h.val.1.stage.val

def childWidth (ε : ℝ) (h : Active K tick) : ℝ := pairWidth ε h / 8

theorem pairWidth_pos {ε : ℝ} (hε : 0 < ε) (h : Active K tick) :
    0 < pairWidth ε h := by
  unfold pairWidth
  positivity

theorem childWidth_pos {ε : ℝ} (hε : 0 < ε) (h : Active K tick) :
    0 < childWidth ε h := div_pos (pairWidth_pos hε h) (by norm_num)

def classStatistic (c : Classes K tick) : Letters c → Statistic c.1 := statistic c.1

def leftSymbol (i : MaskIndex K tick) (c : Classes K tick) : Statistic c.1 := i.2.1 c.1

def rightSymbol (i : MaskIndex K tick) (c : Classes K tick) : Statistic c.1 := i.2.2 c.1

def leftProbability (side : Fin 3) (i : MaskIndex K tick) (c : Classes K tick) : ℝ :=
  leftLaw c.1 c.2 side (leftSymbol i c)

def rightProbability (side : Fin 3) (i : MaskIndex K tick) (c : Classes K tick) : ℝ :=
  rightLaw c.1 c.2 side (rightSymbol i c)

def center (allocation : Allocation) (side : Fin 3) (i : MaskIndex K tick) : ℝ :=
  classProductMixture (fun c : testedClasses allocation i => Positions allocation 1 c.val)
    (fun c => leftProbability side i c.val) (fun c => rightProbability side i c.val)

def passes (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : Words (K := K) (tick := tick) allocation m) : Prop :=
  ∀ i : MaskIndex K tick, ¬ selectedWordPairMaskBad (testedClasses allocation i)
    classStatistic classStatistic (leftSymbol i) (rightSymbol i)
    (pairWidth ε i.1) (center allocation side i) w

def childWindows (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : Words (K := K) (tick := tick) allocation m) : Prop :=
  HistorySymmetry.childWindows classStatistic classStatistic
    (activeLaw (activeCounts allocation m) (fun c => leftLaw c.1 c.2 side))
    (activeLaw (activeCounts allocation m) (fun c => rightLaw c.1 c.2 side))
    (activeWidth (activeCounts allocation m) (fun c => childWidth ε c.1))
    (activeWidth (activeCounts allocation m) (fun c => childWidth ε c.1)) w

def lossConstant (allocation : Allocation) (ε : ℝ) : ℝ :=
  ∑ i : MaskIndex K tick,
    1 / (2 * selectedBasePopulation allocation (testedClasses allocation i) *
      (pairWidth ε i.1) ^ 2)

theorem lossConstant_nonneg (allocation : Allocation) (ε : ℝ) :
    0 ≤ lossConstant (K := K) (tick := tick) allocation ε := by
  apply Finset.sum_nonneg
  intro i _
  change 0 ≤ 1 / (2 * (selectedBaseCount allocation (testedClasses allocation i) : ℝ) *
    (pairWidth ε i.1) ^ 2)
  exact div_nonneg zero_le_one
    (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (sq_nonneg _))

end MatrixMultiplication.AllFieldHistoryMasks






namespace MatrixMultiplication.AllFieldHistoryMaskLaws

open AllFieldHistory AllFieldHistoryChildLaws AllFieldHistorySupport
open AllFieldHistoryMasks AllFieldHistoryBranchWeights AllFieldParameters
open PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def parentCenter (allocation : Allocation) (side : Fin 3) (h : Active K tick)
    (a b : Statistic h) : ℝ :=
  ∑ u : JointPopulation.Shape,
    (activeCounts allocation 1 h u : ℝ) /
      population allocation 1 (h.val.1.source, h.val.2) *
        (leftLaw h u side a * rightLaw h u side b)

theorem center_eq_parentCenter (allocation : Allocation) (side : Fin 3)
    (i : MaskIndex K tick) :
    center allocation side i = parentCenter allocation side i.1 (i.2.1 i.1) (i.2.2 i.1) := by
  have hw (c : testedClasses allocation i) :
      classWeight (fun c : testedClasses allocation i => Positions allocation 1 c.val) c =
        (activeCounts allocation 1 c.val.1 c.val.2 : ℝ) /
          population allocation 1 (i.1.val.1.source, i.1.val.2) := by
    rw [selected_classWeight_formula allocation (by decide : 0 < (1 : ℕ))]
    simp only [selectedBasePopulation, testedClasses, positiveClasses_baseCount]
  unfold center classProductMixture
  simp_rw [hw]
  let f : Classes K tick → ℝ := fun c =>
    (activeCounts allocation 1 c.1 c.2 : ℝ) /
      population allocation 1 (i.1.val.1.source, i.1.val.2) *
        (leftProbability side i c * rightProbability side i c)
  change (∑ c : testedClasses allocation i, f c.val) = _
  rw [Finset.sum_coe_sort]
  have hzero (c : Classes K tick) :
      (if 0 < activeCounts allocation 1 c.1 c.2 then f c else 0) = f c := by
    split_ifs with hc
    · rfl
    · have hz : activeCounts allocation 1 c.1 c.2 = 0 := Nat.eq_zero_of_not_pos hc
      simp [f, hz]
  simp only [testedClasses, positiveClasses, Finset.sum_filter, ite_and, hzero]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i.1]
  · simp [f, parentCenter, leftProbability, rightProbability, leftSymbol, rightSymbol]
  · intro other _ hne
    simp only [hne, ite_false, Finset.sum_const_zero]
  · simp

def stageBActive (h : APositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageB h).lot (Work.stageB h).stage = tick) :
    Active K tick := ⟨(.stageB h, phi), ht⟩

theorem stageB_leftLaw_branch (h : APositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageB h).lot (Work.stageB h).stage = tick)
    (k : BSplit h) (side : Fin 3) (a : Fin 6) :
    leftLaw (stageBActive h phi ht) (branchShape (.stageB h, phi) k) side a =
      (littleLaw (aShape h.val) (bSplit ⟨h, k, false⟩) (phi.symm side) a : ℝ) := by
  change (littleLaw (aShape h.val)
    (canonicalChildShape (.stageB h, phi) (branchShape (.stageB h, phi) k))
    (phi.symm side) a : ℝ) = _
  rw [canonicalChildShape_branchShape (.stageB h, phi) k]
  rfl

theorem stageB_rightLaw_branch (h : APositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageB h).lot (Work.stageB h).stage = tick)
    (k : BSplit h) (side : Fin 3) (b : Fin 6) :
    rightLaw (stageBActive h phi ht) (branchShape (.stageB h, phi) k) side b =
      (littleLaw (aShape h.val) (complement (aShape h.val) (bSplit ⟨h, k, false⟩))
        (phi.symm side) b : ℝ) := by
  change (littleLaw (aShape h.val)
    (complement (aShape h.val)
      (canonicalChildShape (.stageB h, phi) (branchShape (.stageB h, phi) k)))
    (phi.symm side) b : ℝ) = _
  rw [canonicalChildShape_branchShape (.stageB h, phi) k]
  rfl

theorem stageB_sum_laws (h : APositive K) (side : Fin 3) (a b : Fin 6) :
    (∑ k : BSplit h,
      stageBLaw (aShape h.val) (bSplit ⟨h, k, false⟩) *
        littleLaw (aShape h.val) (bSplit ⟨h, k, false⟩) side a *
        littleLaw (aShape h.val) (complement (aShape h.val) (bSplit ⟨h, k, false⟩)) side b) =
      halfLaw (aShape h.val) side (a, b) := by
  rw [halfLaw_positive_parent _ h.property]
  unfold positiveHalfLaw
  change (∑ k : Fin (below (aShape h.val)).length,
    stageBLaw (aShape h.val) (below (aShape h.val))[k.val] *
      littleLaw (aShape h.val) (below (aShape h.val))[k.val] side a *
      littleLaw (aShape h.val) (complement (aShape h.val) (below (aShape h.val))[k.val]) side b) = _
  exact Fin.sum_univ_fun_getElem (below (aShape h.val))
    (fun u => stageBLaw (aShape h.val) u * littleLaw (aShape h.val) u side a *
      littleLaw (aShape h.val) (complement (aShape h.val) u) side b)

theorem parentCenter_stageB (allocation : Allocation) (h : APositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageB h).lot (Work.stageB h).stage = tick)
    (side : Fin 3) (a b : Fin 6) :
    parentCenter allocation side (stageBActive h phi ht) a b =
      (halfLaw (aShape h.val) (phi.symm side) (a, b) : ℝ) := by
  let w : PlacedWork K := (.stageB h, phi)
  let f : JointPopulation.Shape → ℝ := fun u =>
    leftLaw (stageBActive h phi ht) u side a * rightLaw (stageBActive h phi ht) u side b
  calc
    parentCenter allocation side (stageBActive h phi ht) a b =
        (∑ u, (jointCounts allocation 1 w u : ℝ) * f u) /
          population allocation 1 (.afterA h.val, phi) := by
      unfold parentCenter
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro u _
      dsimp only [activeCounts, stageBActive, w, f, Work.source]
      ring
    _ = (∑ k : BSplit h, (branchPopulation allocation 1 w k : ℝ) * f (branchShape w k)) /
          population allocation 1 (.afterA h.val, phi) := by
      rw [jointCounts, shapeCounts_weighted_sum]
      rfl
    _ = ∑ k : BSplit h,
        (stageBLaw (aShape h.val) (bSplit ⟨h, k, false⟩) : ℝ) *
          (littleLaw (aShape h.val) (bSplit ⟨h, k, false⟩) (phi.symm side) a : ℝ) *
          (littleLaw (aShape h.val) (complement (aShape h.val) (bSplit ⟨h, k, false⟩))
            (phi.symm side) b : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [f, w]
      rw [stageB_leftLaw_branch, stageB_rightLaw_branch]
      rw [mul_div_right_comm,
        stageB_branchWeight_real allocation (by decide : 0 < (1 : ℕ)) h k phi]
      ring
    _ = (halfLaw (aShape h.val) (phi.symm side) (a, b) : ℝ) := by
      exact_mod_cast stageB_sum_laws h (phi.symm side) a b

theorem center_stageB (allocation : Allocation) (h : APositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageB h).lot (Work.stageB h).stage = tick)
    (side : Fin 3) (a b : SymbolChoice K tick) :
    center allocation side (stageBActive h phi ht, a, b) =
      (halfLaw (aShape h.val) (phi.symm side)
        (a (stageBActive h phi ht), b (stageBActive h phi ht)) : ℝ) := by
  rw [center_eq_parentCenter]
  exact parentCenter_stageB allocation h phi ht side _ _

end MatrixMultiplication.AllFieldHistoryMaskLaws






namespace MatrixMultiplication.AllFieldHistoryRawMasks

open AllFieldHistory AllFieldHistoryChildLaws AllFieldHistorySupport AllFieldHistoryMasks
open JointCanonicalization PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def rawPairCount (allocation : Allocation) (m : ℕ) (i : MaskIndex K tick)
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m) : ℝ :=
  ∑ j : JointPopulation.Positions (activeCounts allocation m) i.1,
    if statistic i.1 (w i.1 j).1 = i.2.1 i.1 ∧
      statistic i.1 (w i.1 j).2 = i.2.2 i.1 then 1 else 0

def rawPass (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m) : Prop :=
  ∀ i : MaskIndex K tick,
    |rawPairCount allocation m i w /
      (population allocation m (i.1.val.1.source, i.1.val.2) : ℝ) -
        center allocation side i| ≤ pairWidth ε i.1

theorem sum_positiveClasses (allocation : Allocation) (m : ℕ) (h : Active K tick)
    (f : ∀ c : Classes K tick, Positions allocation m c → ℝ) :
    (∑ c : positiveClasses allocation h, ∑ j, f c.val j) =
      ∑ u : JointPopulation.Shape, ∑ j, f (h, u) j := by
  have hzero (c : Classes K tick) (hc : ¬0 < activeCounts allocation 1 c.1 c.2) :
      (∑ j, f c j) = 0 := by
    have hcount : activeCounts allocation m c.1 c.2 = 0 := by
      rw [activeCounts_dilation, Nat.eq_zero_of_not_pos hc, mul_zero]
    apply Finset.sum_eq_zero
    intro j _
    have hj : j.val < 0 := by simpa only [hcount] using j.isLt
    exact (Nat.not_lt_zero _ hj).elim
  rw [Finset.sum_coe_sort (positiveClasses allocation h)
    (fun c : Classes K tick => ∑ j, f c j)]
  unfold positiveClasses
  rw [Finset.sum_filter]
  calc
    (∑ c : Classes K tick,
        if c.1 = h ∧ 0 < activeCounts allocation 1 c.1 c.2 then ∑ j, f c j else 0) =
        ∑ c : Classes K tick, if c.1 = h then ∑ j, f c j else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : 0 < activeCounts allocation 1 c.1 c.2
      · simp only [hc, and_true]
      · rw [hzero c hc]
        simp
    _ = ∑ u : JointPopulation.Shape, ∑ j, f (h, u) j := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single h]
      · simp
      · intro other _ hne
        simp only [hne, ite_false, Finset.sum_const_zero]
      · simp

theorem selectedWordPairCount_pairEquiv (allocation : Allocation) (m : ℕ)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation m))
    (i : MaskIndex K tick) (w : ActiveRawPairs (K := K) (tick := tick) allocation m) :
    selectedWordPairCount (testedClasses allocation i)
      (pairEquiv (activeCounts allocation m)
        (JointCanonicalCW.Left activeHalfLength) (JointCanonicalCW.Right activeHalfLength) e w)
      classStatistic classStatistic (leftSymbol i) (rightSymbol i) =
        rawPairCount allocation m i w := by
  let v : Words (K := K) (tick := tick) allocation m :=
    pairEquiv (activeCounts allocation m)
      (JointCanonicalCW.Left activeHalfLength) (JointCanonicalCW.Right activeHalfLength) e w
  have hsum := sum_positiveClasses allocation m i.1 (fun c j =>
    if classStatistic c (v.left c j) = leftSymbol i c ∧
      classStatistic c (v.right c j) = rightSymbol i c then (1 : ℝ) else 0)
  unfold selectedWordPairCount
  rw [testedClasses, hsum]
  unfold rawPairCount
  rw [← Fintype.sum_sigma']
  apply Fintype.sum_equiv (positionEquiv (activeCounts allocation m) e i.1).symm
  rintro ⟨u, j⟩
  rfl

theorem testedClasses_populationSize (allocation : Allocation) (m : ℕ)
    (i : MaskIndex K tick) :
    populationSize (fun c : testedClasses allocation i => Positions allocation m c.val) =
      (population allocation m (i.1.val.1.source, i.1.val.2) : ℝ) := by
  change populationSize (selectedPositions allocation m (positiveClasses allocation i.1)) = _
  rw [positiveClasses_populationSize, population_dilation allocation m, Nat.cast_mul]
  exact mul_comm _ _

theorem raw_population_pos (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    (h : Active K tick) :
    0 < (population allocation m (h.val.1.source, h.val.2) : ℝ) := by
  exact_mod_cast AllFieldHistorySupport.work_source_population_pos allocation hm h.val

theorem passes_pairEquiv_iff_rawPass (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (side : Fin 3)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation m))
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m) :
    passes allocation m ε side
      (pairEquiv (activeCounts allocation m)
        (JointCanonicalCW.Left activeHalfLength) (JointCanonicalCW.Right activeHalfLength) e w) ↔
      rawPass allocation m ε side w := by
  simp only [passes, selectedWordPairMaskBad, selectedWordPairCount_pairEquiv,
    testedClasses_populationSize, rawPass, not_lt]

theorem passes_pairEquiv_target_independent (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (side : Fin 3)
    (e f : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation m))
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m) :
    passes allocation m ε side
      (pairEquiv (activeCounts allocation m)
        (JointCanonicalCW.Left activeHalfLength) (JointCanonicalCW.Right activeHalfLength) e w) ↔
    passes allocation m ε side
      (pairEquiv (activeCounts allocation m)
        (JointCanonicalCW.Left activeHalfLength) (JointCanonicalCW.Right activeHalfLength) f w) :=
  (passes_pairEquiv_iff_rawPass allocation m ε side e w).trans
    (passes_pairEquiv_iff_rawPass allocation m ε side f w).symm

end MatrixMultiplication.AllFieldHistoryRawMasks






namespace MatrixMultiplication.AllFieldHistoryIncomingMasks

open MatrixMultiplication.Foundation AllFieldHistory AllFieldParameters
open AllFieldHistoryChildLaws AllFieldHistorySupport AllFieldHistoryMasks
open AllFieldHistoryMaskLaws AllFieldHistoryRawMasks InheritedMasks
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem empiricalLaw_congr_decidable {P A : Type*} [Fintype P]
    (d₁ d₂ : DecidableEq A) (w : P → A) (a : A) :
    @empiricalLaw P A _ d₁ w a = @empiricalLaw P A _ d₂ w a := by
  cases Subsingleton.elim d₁ d₂
  rfl

theorem typeWindow_mono_decidable {P A : Type*} [Fintype P]
    (d₁ d₂ : DecidableEq A) (ν : A → ℝ) {η δ : ℝ} (hη : η ≤ δ)
    (w : P → A) (hw : @typeWindow P A _ d₁ ν η w) :
    @typeWindow P A _ d₂ ν δ w := by
  cases Subsingleton.elim d₁ d₂
  intro a
  exact (hw a).trans hη

theorem weight_append {m n : ℕ} (l : Fin m → Fin 7) (r : Fin n → Fin 7) :
    CWStrands.weight (Fin.append l r) = CWStrands.weight l + CWStrands.weight r := by
  simp [CWStrands.weight, Fin.sum_univ_add]

theorem strand_append {F : Type*} [CommRing F] {m n : ℕ}
    (x y z : (Fin m → Fin 7) × (Fin n → Fin 7)) :
    CWStrands.strand (F := F) (Fin (m + n))
      (Fin.append x.1 x.2) (Fin.append y.1 y.2) (Fin.append z.1 z.2) =
        CWStrands.strand (Fin m) x.1 y.1 z.1 * CWStrands.strand (Fin n) x.2 y.2 z.2 := by
  simp [CWStrands.strand, Fin.prod_univ_add]

theorem shapeTensor_append {F : Type*} [CommRing F] {m n : ℕ} (g : Shape)
    (x y z : (Fin m → Fin 7) × (Fin n → Fin 7)) :
    CWStrands.shapeTensor (F := F) (Fin (m + n)) g
      (Fin.append x.1 x.2) (Fin.append y.1 y.2) (Fin.append z.1 z.2) =
        CWStrands.shapeTensor (Fin m ⊕ Fin n) g
          (Sum.elim x.1 x.2) (Sum.elim y.1 y.2) (Sum.elim z.1 z.2) := by
  simp only [CWStrands.shapeTensor, weight_append, CWStrands.weight_sum_elim,
    strand_append, CWStrands.strand_sum_elim, Tensor.product]

theorem shapeTensor_joinHalves {F : Type*} [CommRing F] (w : Work K) (g : Shape)
    (x y z : (Fin w.halfLength → Fin 7) × (Fin w.halfLength → Fin 7)) :
    CWStrands.shapeTensor (F := F) (Fin (currentLength w.source)) g
      (joinHalves w x) (joinHalves w y) (joinHalves w z) =
        CWStrands.shapeTensor (Fin w.halfLength ⊕ Fin w.halfLength) g
          (Sum.elim x.1 x.2) (Sum.elim y.1 y.2) (Sum.elim z.1 z.2) := by
  cases w <;> exact shapeTensor_append g x y z

def defaultStatistic : (w : Work K) → w.Statistic
  | .stageA _ => (0, 0)
  | .stageB _ => (0 : Fin 6)
  | .stageC _ => PUnit.unit

def choiceAt (h : Active K tick) (a : Statistic h) : SymbolChoice K tick :=
  Function.update (fun g => defaultStatistic g.val.1) h a

@[simp] theorem choiceAt_self (h : Active K tick) (a : Statistic h) :
    choiceAt h a h = a := by simp [choiceAt]

theorem rawPairCount_eq_wordPopulation (allocation : Allocation) (m : ℕ)
    (i : MaskIndex K tick) (w : ActiveRawPairs (K := K) (tick := tick) allocation m) :
    rawPairCount allocation m i w =
      (wordPopulation (fun j => (statistic i.1 (w i.1 j).1,
        statistic i.1 (w i.1 j).2)) (i.2.1 i.1, i.2.2 i.1) : ℝ) := by
  simp only [rawPairCount, wordPopulation, Fintype.card_subtype, Prod.mk.injEq]
  exact Finset.sum_boole _ _

@[simp] theorem fourStatistic_append (l r : Fin 2 → Fin 7) :
    CWCompleteStatistics.fourStatistic (Fin.append l r) =
      (CWCompleteStatistics.twoStatistic l, CWCompleteStatistics.twoStatistic r) := rfl

@[simp] theorem append_singletons (l r : Fin 1 → Fin 7) :
    Fin.append l r = (Matrix.vecCons (l 0) (Matrix.vecCons (r 0) Matrix.vecEmpty)) := by
  funext i
  fin_cases i <;> rfl

attribute [local irreducible] activeCounts population

theorem rawPass_stageB_typeWindow (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (side : Fin 3) (w : ActiveRawPairs (K := K) (tick := tick) allocation m)
    (hw : rawPass allocation m ε side w) (h : APositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageB h).lot (Work.stageB h).stage = tick) :
    typeWindow (fun ij : PairSlot => (halfLaw (aShape h.val) (phi.symm side) ij : ℝ))
      (pairWidth ε (stageBActive h phi ht))
      (fun j => CWCompleteStatistics.fourStatistic
        (joinHalves (.stageB h) (w (stageBActive h phi ht) j))) := by
  intro ij
  have hp := hw (stageBActive h phi ht,
    choiceAt (stageBActive h phi ht) ij.1, choiceAt (stageBActive h phi ht) ij.2)
  rw [center_stageB] at hp
  rw [rawPairCount_eq_wordPopulation] at hp
  erw [choiceAt_self, choiceAt_self] at hp
  have hcard : Fintype.card (JointPopulation.Positions (activeCounts allocation m)
      (stageBActive h phi ht)) = population allocation m (.afterA h.val, phi) := by
    simp only [Fintype.card_eq_nat_card]
    simp only [JointPopulation.Positions, Nat.card_fin]
    simpa only [activeCounts, stageBActive, Work.source] using
      jointCounts_sum allocation m (.stageB h, phi)
  have hword : (fun j => CWCompleteStatistics.fourStatistic
      (joinHalves (.stageB h) (w (stageBActive h phi ht) j))) =
      (fun j => (statistic (stageBActive h phi ht) (w (stageBActive h phi ht) j).1,
        statistic (stageBActive h phi ht) (w (stageBActive h phi ht) j).2)) := by
    funext j
    rfl
  have he : empiricalLaw (fun j => CWCompleteStatistics.fourStatistic
      (joinHalves (.stageB h) (w (stageBActive h phi ht) j))) ij =
      empiricalLaw (fun j =>
        (statistic (stageBActive h phi ht) (w (stageBActive h phi ht) j).1,
          statistic (stageBActive h phi ht) (w (stageBActive h phi ht) j).2)) ij := by
    rw [hword]
    exact empiricalLaw_congr_decidable _ _ _ _
  rw [he]
  unfold empiricalLaw
  rw [hcard]
  dsimp only [stageBActive, Work.source] at hp
  erw [choiceAt_self, choiceAt_self] at hp
  exact hp

theorem incoming_stageA (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (side : Fin 3) (w : ActiveRawPairs (K := K) (tick := tick) allocation m)
    (h : InitialPositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageA h).lot (Work.stageA h).stage = tick) :
    residentMask allocation m ε ((Work.stageA h).source, phi) side
      (incomingWord allocation m ⟨(.stageA h, phi), ht⟩ w) := by
  trivial

theorem incoming_stageB (allocation : Allocation) (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (side : Fin 3) (w : ActiveRawPairs (K := K) (tick := tick) allocation m)
    (hw : rawPass allocation m ε side w) (h : APositive K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageB h).lot (Work.stageB h).stage = tick) :
    residentMask allocation m ε ((Work.stageB h).source, phi) side
      (incomingWord allocation m (stageBActive h phi ht) w) := by
  intro _
  have hraw := rawPass_stageB_typeWindow allocation m ε side w hw h phi ht
  have htransport := (JointCanonicalization.typeWindow_reindex
    (fun ij : PairSlot => (halfLaw (aShape h.val) (phi.symm side) ij : ℝ))
    (pairWidth ε (stageBActive h phi ht))
    (fun j => CWCompleteStatistics.fourStatistic
      (joinHalves (.stageB h) (w (stageBActive h phi ht) j)))
    (sourcePositionsEquiv allocation m (stageBActive h phi ht)).symm).2 hraw
  have hwidth : pairWidth ε (stageBActive h phi ht) ≤ ε / 8 := by
    change ε / 16 ^ 1 ≤ ε / 8
    norm_num
    linarith
  dsimp only [Work.source, residentLaw, residentLawRat, residentWidth, residentStatistic]
  exact typeWindow_mono_decidable _ _ _ hwidth _ htransport

theorem incoming_stageC (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation m))
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m)
    (h : PartC K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageC h).lot (Work.stageC h).stage = tick)
    (hweights : ∀ j,
      CWLeafStatistics.weight ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).1 (0 : Fin 1)) =
        (JointPopulation.shapeSide side ((e (AllFieldHistoryStageCIncoming.stageCActive h phi ht)).val j)).val ∧
      CWLeafStatistics.weight ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).2 (0 : Fin 1)) =
        activeParentShape (AllFieldHistoryStageCIncoming.stageCActive h phi ht) side -
          (JointPopulation.shapeSide side ((e (AllFieldHistoryStageCIncoming.stageCActive h phi ht)).val j)).val) :
    residentMask allocation m ε ((Work.stageC h).source, phi) side
      (incomingWord allocation m (AllFieldHistoryStageCIncoming.stageCActive h phi ht) w) := by
  intro _
  have hraw := AllFieldHistoryStageCIncoming.typeWindow_of_target_side_weights
    allocation hm h phi ht e w side hweights (ε / 256) (div_nonneg hε (by norm_num))
  have htransport := (JointCanonicalization.typeWindow_reindex
    (fun a : Fin 6 => (littleLaw (cParameterParent h) (cShapeParent h) (phi.symm side) a : ℝ))
    (ε / 256)
    (fun j => CWCompleteStatistics.twoStatistic
      (Matrix.vecCons ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).1 (0 : Fin 1)) (Matrix.vecCons ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).2 (0 : Fin 1)) Matrix.vecEmpty)))
    (sourcePositionsEquiv allocation m (AllFieldHistoryStageCIncoming.stageCActive h phi ht)).symm).2 hraw
  have hword : incomingWord allocation m
      (AllFieldHistoryStageCIncoming.stageCActive h phi ht) w =
      fun position => Matrix.vecCons
        ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht)
          ((sourcePositionsEquiv allocation m
            (AllFieldHistoryStageCIncoming.stageCActive h phi ht)).symm position)).1 (0 : Fin 1))
        (Matrix.vecCons
          ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht)
            ((sourcePositionsEquiv allocation m
              (AllFieldHistoryStageCIncoming.stageCActive h phi ht)).symm position)).2 (0 : Fin 1))
          Matrix.vecEmpty) := by
    funext position
    exact append_singletons _ _
  rw [hword]
  dsimp only [Work.source, residentLaw, residentLawRat, residentWidth, residentStatistic]
  exact typeWindow_mono_decidable _ _ _ le_rfl _ htransport

def stageCWeights (allocation : Allocation) (m : ℕ) (side : Fin 3)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation m))
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m) : Prop :=
  ∀ (h : PartC K) (phi : Placement)
    (ht : FiniteSchedule.lotTick (Work.stageC h).lot (Work.stageC h).stage = tick) j,
      CWLeafStatistics.weight ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).1 (0 : Fin 1)) =
        (JointPopulation.shapeSide side ((e (AllFieldHistoryStageCIncoming.stageCActive h phi ht)).val j)).val ∧
      CWLeafStatistics.weight ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).2 (0 : Fin 1)) =
        activeParentShape (AllFieldHistoryStageCIncoming.stageCActive h phi ht) side -
          (JointPopulation.shapeSide side ((e (AllFieldHistoryStageCIncoming.stageCActive h phi ht)).val j)).val

theorem received_of_rawPass (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (e : JointPopulation.Target (activeCounts (K := K) (tick := tick) allocation m))
    (w : ActiveRawPairs (K := K) (tick := tick) allocation m)
    (hw : rawPass allocation m ε side w) (hc : stageCWeights allocation m side e w) :
    received allocation m ε side w := by
  rintro ⟨⟨work, phi⟩, ht⟩
  cases work with
  | stageA h => exact incoming_stageA allocation m ε side w h phi ht
  | stageB h => exact incoming_stageB allocation m hε side w hw h phi ht
  | stageC h => exact incoming_stageC allocation hm hε side e w h phi ht (hc h phi ht)

end MatrixMultiplication.AllFieldHistoryIncomingMasks

end
end




section
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.EquivOrbitTransport

variable {G X Y : Type*} [Group G] [MulAction G Y]

@[instance_reducible] def action (e : X ≃ Y) : MulAction G X where
  smul g x := e.symm (g • e x)
  one_smul x := by
    change e.symm ((1 : G) • e x) = x
    simp
  mul_smul g h x := by
    change e.symm ((g * h) • e x) = e.symm (g • e (e.symm (h • e x)))
    simp [mul_smul]

@[simp] theorem equiv_smul (e : X ≃ Y) (g : G) (x : X) :
    letI : MulAction G X := action e
    e (g • x) = g • e x := by
  exact e.apply_symm_apply _

section Finite

variable [Fintype G] [DecidableEq X] [DecidableEq Y]

theorem orbitSet_map (e : X ≃ Y) (x : X) :
    letI : MulAction G X := action e
    (OrbitCounting.orbitSet (G := G) x).map e.toEmbedding =
      OrbitCounting.orbitSet (G := G) (e x) := by
  let : MulAction G X := action e
  change (Finset.univ.image fun g : G => e.symm (g • e x)).map e.toEmbedding = _
  simp only [Finset.map_eq_image, Finset.image_image, Function.comp_def,
    Equiv.toEmbedding_apply, Equiv.apply_symm_apply, OrbitCounting.orbitSet]

theorem orbitSet_card (e : X ≃ Y) (x : X) :
    letI : MulAction G X := action e
    (OrbitCounting.orbitSet (G := G) x).card =
      (OrbitCounting.orbitSet (G := G) (e x)).card := by
  let : MulAction G X := action e
  simpa only [Finset.card_map] using congrArg Finset.card (orbitSet_map e x)

theorem rejected_card (e : X ≃ Y) (bad : X → Prop) [DecidablePred bad] (x : X) :
    letI : MulAction G X := action e
    ((OrbitCounting.orbitSet (G := G) x).filter bad).card =
      ((OrbitCounting.orbitSet (G := G) (e x)).filter (bad ∘ e.symm)).card := by
  let : MulAction G X := action e
  calc
    ((OrbitCounting.orbitSet (G := G) x).filter bad).card =
        (((OrbitCounting.orbitSet (G := G) x).filter bad).map e.toEmbedding).card :=
      (Finset.card_map _).symm
    _ = _ := by rw [Finset.map_filter, orbitSet_map]

theorem rejected_fraction (e : X ≃ Y) (bad : X → Prop) [DecidablePred bad] (x : X) :
    letI : MulAction G X := action e
    (((OrbitCounting.orbitSet (G := G) x).filter bad).card : ℝ) /
        (OrbitCounting.orbitSet (G := G) x).card =
      (((OrbitCounting.orbitSet (G := G) (e x)).filter (bad ∘ e.symm)).card : ℝ) /
        (OrbitCounting.orbitSet (G := G) (e x)).card := by
  let : MulAction G X := action e
  rw [rejected_card e bad x, orbitSet_card e x]

end Finite

theorem coefficients_preserved
    {K RX RY RZ CX CY CZ : Type*} [CommSemiring K]
    [MulAction G CX] [MulAction G CY] [MulAction G CZ]
    (ex : RX ≃ CX) (ey : RY ≃ CY) (ez : RZ ≃ CZ)
    (raw : Tensor K RX RY RZ) (canonical : Tensor K CX CY CZ)
    (hcoords : ∀ x y z, raw x y z = canonical (ex x) (ey y) (ez z))
    (hcanonical : ∀ (g : G) x y z,
      canonical (g • x) (g • y) (g • z) = canonical x y z) :
    letI : MulAction G RX := action ex
    letI : MulAction G RY := action ey
    letI : MulAction G RZ := action ez
    ∀ (g : G) x y z, raw (g • x) (g • y) (g • z) = raw x y z := by
  let : MulAction G RX := action ex
  let : MulAction G RY := action ey
  let : MulAction G RZ := action ez
  intro g x y z
  rw [hcoords, hcoords]
  change canonical (ex (ex.symm (g • ex x))) (ey (ey.symm (g • ey y)))
    (ez (ez.symm (g • ez z))) = _
  simpa only [Equiv.apply_symm_apply] using hcanonical g (ex x) (ey y) (ez z)

end MatrixMultiplication.EquivOrbitTransport

end




section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryRecovery

open MatrixMultiplication.Foundation AllFieldHistory AllFieldHistoryChildLaws
open AllFieldHistorySupport JointPopulation JointCanonicalization JointCanonicalCW
open PermutationMatching
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem halfLength_le_eight (h : Active K tick) : activeHalfLength h ≤ 8 := by
  rcases h with ⟨⟨w, phi⟩, hh⟩
  cases w <;> norm_num [activeHalfLength, Work.halfLength]

abbrev Raw (allocation : Allocation) (m : ℕ) :=
  ActiveRawPairs (K := K) (tick := tick) allocation m

abbrev Targets (allocation : Allocation) (m : ℕ) :=
  Target (activeCounts (K := K) (tick := tick) allocation m)

abbrev Symmetries (allocation : Allocation) (m : ℕ) :=
  HalfClassPermutations (ClassPositions
    (activeCounts (K := K) (tick := tick) allocation m))

def childStatistic (_side : Fin 3) (c : Active K tick × JointPopulation.Shape) :=
  statistic c.1

def leftPrescription (side : Fin 3) (c : Active K tick × JointPopulation.Shape) :=
  leftLaw c.1 c.2 side

def rightPrescription (side : Fin 3) (c : Active K tick × JointPopulation.Shape) :=
  rightLaw c.1 c.2 side

def outputWidth (ε : ℝ) (_side : Fin 3) (c : Active K tick × JointPopulation.Shape) :=
  AllFieldHistoryMasks.childWidth ε c.1

def parents (F : Type*) [CommRing F] (h : Active K tick) :=
  JointCanonicalMixed.inputTensor (F := F) activeHalfLength activeHalfLength
    activeParentShape (fun _ => true) h

def rawSource (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ) :
    Tensor F (Raw (K := K) (tick := tick) allocation m)
      (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) :=
  sourceTensor (activeCounts allocation m) (Left activeHalfLength)
    (Right activeHalfLength) (parents F)

def ideal (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (e : Targets (K := K) (tick := tick) allocation m) :
    Tensor F (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) :=
  JointCanonicalization.ideal (activeCounts allocation m)
    (Left activeHalfLength) (Right activeHalfLength) (parents F)
    (coarse activeHalfLength activeHalfLength halfLength_le_eight)
    childStatistic childStatistic leftPrescription rightPrescription
    (outputWidth ε) (outputWidth ε) e

def coordinates (allocation : Allocation) (m : ℕ)
    (e : Targets (K := K) (tick := tick) allocation m) :=
  pairEquiv (activeCounts allocation m) (Left activeHalfLength)
    (Right activeHalfLength) e

def canonical (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ) (ε : ℝ) :
    Tensor F (AllFieldHistoryMasks.Words (K := K) (tick := tick) allocation m)
      (AllFieldHistoryMasks.Words (K := K) (tick := tick) allocation m) (AllFieldHistoryMasks.Words (K := K) (tick := tick) allocation m) :=
  canonicalIdeal (activeCounts allocation m) (Left activeHalfLength)
    (Right activeHalfLength) (parents F)
    (coarse activeHalfLength activeHalfLength halfLength_le_eight)
    childStatistic childStatistic leftPrescription rightPrescription
    (outputWidth ε) (outputWidth ε)

@[instance_reducible] def rawAction (allocation : Allocation) (m : ℕ)
    (e : Targets (K := K) (tick := tick) allocation m) :
    MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) :=
  EquivOrbitTransport.action (coordinates allocation m e)

def completeKeep (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (w : Raw (K := K) (tick := tick) allocation m) : Prop :=
  JointCanonicalMixed.sideMask (activeCounts allocation m)
      activeHalfLength activeHalfLength halfLength_le_eight side w ∧
    AllFieldHistoryIncomingMasks.received allocation m ε side w ∧
    AllFieldHistoryRawMasks.rawPass allocation m ε side w

def sideVariable {V : Type*} (side : Fin 3) (x y z : V) : V := (Matrix.vecCons (x) (Matrix.vecCons (y) (Matrix.vecCons (z) Matrix.vecEmpty))) side

def idealSide (allocation : Allocation) (m : ℕ) (ε : ℝ) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m) (w : Raw (K := K) (tick := tick) allocation m) : Prop :=
  coarseMask (activeCounts allocation m) (Left activeHalfLength) (Right activeHalfLength)
      (coarse activeHalfLength activeHalfLength halfLength_le_eight) side e w ∧
    rawWindows (activeCounts allocation m) (Left activeHalfLength) (Right activeHalfLength)
      (childStatistic side) (childStatistic side) (leftPrescription side)
      (rightPrescription side) (outputWidth ε side) (outputWidth ε side) e w

end MatrixMultiplication.AllFieldHistoryRecovery






namespace MatrixMultiplication.AllFieldHistoryRecovery

open AllFieldHistory AllFieldHistorySupport

attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def minimumDilation (allocation : Allocation) (ε : ℝ) : ℕ :=
  Nat.ceil (3 * (AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε + 6)) + 2

theorem minimumDilation_spec (allocation : Allocation) (ε : ℝ) {m : ℕ}
    (hm : minimumDilation (K := K) (tick := tick) allocation ε ≤ m) :
    2 ≤ m ∧
      3 * (AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε + 6) <
        (m : ℝ) := by
  constructor
  · exact (Nat.le_add_left 2 _).trans hm
  · have hc := Nat.le_ceil
      (3 * (AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε + 6))
    have hm' : (Nat.ceil
        (3 * (AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε + 6)) : ℝ) + 2 ≤ m := by
      exact_mod_cast hm
    linarith

def shiftCount (allocation : Allocation) (ε : ℝ) (m : ℕ) : ℕ :=
  RecoveryGrowth.shiftCount (supportRate (K := K) (tick := tick) allocation)
    (AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε + 6) m

theorem replication_subexponential (allocation : Allocation) (ε : ℝ) :
    Filter.Tendsto (fun m : ℕ =>
      Real.log (Fintype.card (InverseLinearRecovery.MaskRectangles
        (shiftCount (K := K) (tick := tick) allocation ε m))) / m)
      Filter.atTop (nhds 0) :=
  InverseLinearRecovery.subexponential_copies (supportRate_pos allocation)
    (by have := AllFieldHistoryMasks.lossConstant_nonneg (K := K) (tick := tick) allocation ε
        linarith)

end MatrixMultiplication.AllFieldHistoryRecovery

end
end

end MatrixAllFields

end OAI
