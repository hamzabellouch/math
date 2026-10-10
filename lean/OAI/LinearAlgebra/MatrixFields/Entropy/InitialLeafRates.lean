import Mathlib
import OAI.LinearAlgebra.MatrixFields.Histories.HistorySums
import OAI.LinearAlgebra.MatrixFields.Tensors.CWWordDimensionParameters

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldParameters

open MatrixMultiplication.Foundation
open scoped BigOperators

noncomputable section

theorem entropy_two_points {A : Type*} [Fintype A] [DecidableEq A]
    (a b : A) (hab : a ≠ b) (p q : ℝ) :
    finiteEntropy (fun i => if i = a then p else if i = b then q else 0) =
      entropyTerm p + entropyTerm q := by
  unfold finiteEntropy
  calc
    _ = ∑ i : A, ((if i = a then entropyTerm p else 0) +
        (if i = b then entropyTerm q else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = a
      · subst i
        simp [hab]
      · by_cases hj : i = b
        · subst i
          simp [hab.symm]
        · simp [hi, hj]
    _ = _ := by simp [Finset.sum_add_distrib]

theorem weighted_two_points {A : Type*} [Fintype A] [DecidableEq A]
    (a b : A) (hab : a ≠ b) (p q : ℝ) (f : A → ℝ) :
    (∑ i : A, (if i = a then p else if i = b then q else 0) * f i) =
      p * f a + q * f b := by
  calc
    _ = ∑ i : A, ((if i = a then p * f a else 0) +
        (if i = b then q * f b else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = a
      · subst i
        simp [hab]
      · by_cases hj : i = b
        · subst i
          simp [hi]
        · simp [hi, hj]
    _ = _ := by simp [Finset.sum_add_distrib]

def statisticRate (d : ℚ) (k : Fin 5) : ℝ :=
  finiteEntropy (fun i : Fin 6 => (statisticLaw d k i : ℝ)) +
    ∑ i : Fin 6, (statisticLaw d k i : ℝ) * Real.log (multiplicity i : ℝ)

def binaryEntropyRate (d : ℚ) : ℝ :=
  entropyTerm (1 - (d : ℝ)) + entropyTerm (d : ℝ) + (d : ℝ) * Real.log 2

theorem statisticLaw_two_real (d : ℚ) (i : Fin 6) :
    (statisticLaw d 2 i : ℝ) =
      if i = 2 then 1 - (d : ℝ) else if i = 3 then (d : ℝ) else 0 := by
  by_cases hi : i = 2
  · simp [statisticLaw, hi]
  · by_cases hj : i = 3 <;> simp [statisticLaw, hi, hj]

theorem statisticRate_two (d : ℚ) :
    statisticRate d 2 = binaryEntropyRate d + 2 * (1 - (d : ℝ)) * Real.log 5 := by
  unfold statisticRate
  simp_rw [statisticLaw_two_real]
  rw [entropy_two_points (2 : Fin 6) 3 (by decide),
    weighted_two_points (2 : Fin 6) 3 (by decide)]
  have h25 : Real.log (25 : ℝ) = 2 * Real.log 5 := by
    have hp : (5 : ℝ) ^ 2 = 25 := by norm_num
    rw [← hp, Real.log_pow]
    norm_num
  change entropyTerm (1 - (d : ℝ)) + entropyTerm (d : ℝ) +
    ((1 - (d : ℝ)) * Real.log 25 + (d : ℝ) * Real.log 2) = _
  rw [h25]
  unfold binaryEntropyRate
  ring

theorem statisticRate_deterministic (d : ℚ) (k : Fin 5) (hk : k.val ≠ 2) :
    statisticRate d k = Real.log (multiplicity (singletonSlot k.val) : ℝ) := by
  have hmass (i : Fin 6) : (statisticLaw d k i : ℝ) =
      if i = singletonSlot k.val then 1 else 0 := by
    by_cases hi : i = singletonSlot k.val <;> simp [statisticLaw, hk, hi]
  unfold statisticRate finiteEntropy
  simp_rw [hmass]
  simp [entropyTerm, apply_ite]

theorem statisticRate_zero (d : ℚ) : statisticRate d 0 = 0 := by
  rw [statisticRate_deterministic d 0 (by decide)]
  norm_num [singletonSlot, multiplicity]

theorem statisticRate_one (d : ℚ) : statisticRate d 1 = Real.log 10 := by
  rw [statisticRate_deterministic d 1 (by decide)]
  norm_num [singletonSlot, multiplicity]

theorem statisticRate_three (d : ℚ) : statisticRate d 3 = Real.log 10 := by
  rw [statisticRate_deterministic d 3 (by decide)]
  change Real.log (10 : ℝ) = Real.log 10
  rfl

theorem statisticRate_four (d : ℚ) : statisticRate d 4 = 0 := by
  rw [statisticRate_deterministic d 4 (by decide)]
  have hv : multiplicity (singletonSlot (4 : Fin 5).val) = 1 := by decide +kernel
  rw [hv]
  norm_num

end

end MatrixMultiplication.AllFieldParameters

noncomputable section

namespace MatrixMultiplication.AllFieldTerminalRates

open AllFieldParameters AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def initialRate (g : Shape) : ℝ :=
  Real.log (Contractions.coefficients[shapeMax g]?.getD 0 : ℝ)

def S0 : ℝ :=
  ((sortedInitial.filter (fun g => !positive g)).map
    (fun g => (initialLaw g : ℝ) * initialRate g)).sum

def S1 : ℝ :=
  (zeroSecond.map (fun t => (secondMass t : ℝ) * AllFieldZeroLeafRates.fourRate t)).sum

def secondLeafRate (t u : Shape) : ℝ :=
  if shapeMax u = 4 then 0
  else if shapeMax u = 3 then Real.log 10
  else if !positive u then
    binaryEntropyRate (binaryParameter t u) +
      2 * (1 - (binaryParameter t u : ℝ)) * Real.log 5
  else (2 - (binaryParameter t u : ℝ)) * Real.log 5

def S2 : ℝ :=
  (positiveSecond.map (fun t =>
    ((below t).map (fun u => (littleMass t u : ℝ) * secondLeafRate t u)).sum)).sum

def S : ℝ := (S0 + S1) + S2

private theorem four_shape_max_lt_five : ∀ u ∈ shapes 4, shapeMax u < 5 := by
  decide +kernel

private theorem four_zero_max : ∀ u ∈ shapes 4, positive u = false →
    shapeMax u = 2 ∨ shapeMax u = 3 ∨ shapeMax u = 4 := by
  decide +kernel

private theorem four_positive_max : ∀ u ∈ shapes 4, positive u = true →
    shapeMax u = 2 := by
  decide +kernel

theorem second_shapeMax_lt_five (t : Shape) (ht : t ∈ positiveSecond)
    (u : Shape) (hu : u ∈ below t) : shapeMax u < 5 :=
  four_shape_max_lt_five u (stageB_children_size t ht u hu)

theorem secondLeafRate_zero (t : Shape) (ht : t ∈ positiveSecond)
    (u : Shape) (hu : u ∈ below t) (hz : positive u = false) :
    secondLeafRate t u = statisticRate (binaryParameter t u)
      ⟨shapeMax u, second_shapeMax_lt_five t ht u hu⟩ := by
  rcases four_zero_max u (stageB_children_size t ht u hu) hz with h2 | h3 | h4
  · have hk : (⟨shapeMax u, second_shapeMax_lt_five t ht u hu⟩ : Fin 5) = 2 :=
      Fin.ext h2
    rw [hk, statisticRate_two]
    simp [secondLeafRate, h2, hz]
  · have hk : (⟨shapeMax u, second_shapeMax_lt_five t ht u hu⟩ : Fin 5) = 3 :=
      Fin.ext h3
    rw [hk, statisticRate_three]
    simp [secondLeafRate, h3]
  · have hk : (⟨shapeMax u, second_shapeMax_lt_five t ht u hu⟩ : Fin 5) = 4 :=
      Fin.ext h4
    rw [hk, statisticRate_four]
    simp [secondLeafRate, h4]

theorem secondLeafRate_positive (t : Shape) (ht : t ∈ positiveSecond)
    (u : Shape) (hu : u ∈ below t) (hp : positive u = true) :
    secondLeafRate t u = (2 - (binaryParameter t u : ℝ)) * Real.log 5 := by
  have hm := four_positive_max u (stageB_children_size t ht u hu) hp
  simp [secondLeafRate, hm, hp]

theorem secondLeafRate_builder_expression (t u : Shape) :
    secondLeafRate t u =
      if shapeMax u = 4 then 0
      else if shapeMax u = 3 then Real.log 10
      else if !positive u then
        (MatrixMultiplication.Foundation.entropyTerm (1 - (binaryParameter t u : ℝ)) +
          MatrixMultiplication.Foundation.entropyTerm (binaryParameter t u : ℝ) +
          (binaryParameter t u : ℝ) * Real.log 2) +
          ((1 - (binaryParameter t u : ℝ)) * 2) * Real.log 5
      else (2 - (binaryParameter t u : ℝ)) * Real.log 5 := by
  unfold secondLeafRate
  split_ifs <;> try rfl
  unfold binaryEntropyRate
  ring

private theorem list_filter_sum_inline_MatrixMultiplication_AllFieldTerminalRateFormulas {A : Type*} (xs : List A) (p : A → Bool)
    (f : A → ℝ) :
    ((xs.filter p).map f).sum = (xs.map (fun a => if p a then f a else 0)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => cases hp : p a <;> simp [hp, ih]

theorem initial_zero_history_rate (K : ℕ) :
    (∑ h : {h : Initial K // initialShape h ∉ positiveInitial},
      (initialAmount h.val : ℝ) * initialRate (initialShape h.val)) = (K : ℝ) * S0 := by
  calc
    _ = ∑ h : Initial K, if initialShape h ∉ positiveInitial then
        (initialAmount h : ℝ) * initialRate (initialShape h) else 0 := by
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype
        (p := fun h : Initial K => initialShape h ∉ positiveInitial)
        (Finset.univ.filter (fun h : Initial K => initialShape h ∉ positiveInitial))
        (by simp)
        (fun h : Initial K => (initialAmount h : ℝ) * initialRate (initialShape h))).symm
    _ = ∑ h : Initial K, (initialAmount h : ℝ) *
        (if initialShape h ∉ positiveInitial then initialRate (initialShape h) else 0) := by
      apply Finset.sum_congr rfl
      intro h _
      split_ifs <;> simp
    _ = _ := by
      rw [initial_history_sum K
        (fun g => if g ∉ positiveInitial then initialRate g else 0), S0, list_filter_sum_inline_MatrixMultiplication_AllFieldTerminalRateFormulas]
      apply congrArg (fun x : ℝ => (K : ℝ) * x)
      apply congrArg List.sum
      apply List.map_congr_left
      intro g hg
      cases hp : positive g <;> simp [positiveInitial, hg, hp]

end MatrixMultiplication.AllFieldTerminalRates

namespace MatrixMultiplication.AllFieldInitialLeafRates

open AllFieldHistory AllFieldParameters AllFieldTerminalRates
open CWWindowedLeaves Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev InitialZero (K : ℕ) :=
  {h : Initial K // initialShape h ∉ positiveInitial}

abbrev PopulationHistory (K : ℕ) := InitialZero K × Placement

theorem shapeMax_lt {K : ℕ} (h : InitialZero K) :
    shapeMax (initialShape h.val) < 17 := by
  have hb := (root_shape_spec _ (initialShape_mem h.val)).1
  exact Nat.lt_succ_of_le (max_le (hb 0) (max_le (hb 1) (hb 2)))

def shapeIndex {K : ℕ} (h : InitialZero K) : Fin 17 :=
  ⟨shapeMax (initialShape h.val), shapeMax_lt h⟩

theorem card_alphabet {K : ℕ} (h : InitialZero K) :
    Fintype.card (Alphabet 8 (shapeMax (initialShape h.val))) =
      Contractions.coefficients[shapeMax (initialShape h.val)]?.getD 0 := by
  have hc := CWWordDimensionParameters.table_eq_card (shapeIndex h)
  rw [Fintype.card_eq_nat_card] at hc ⊢
  exact hc.symm

theorem card_alphabet_pos {K : ℕ} (h : InitialZero K) :
    0 < Fintype.card (Alphabet 8 (shapeMax (initialShape h.val))) := by
  have hc := CWWordDimensionParameters.word_card_positive (shapeIndex h)
  rw [Fintype.card_eq_nat_card] at hc ⊢
  exact hc

abbrev Words {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : PopulationHistory K) :=
  Fin (population allocation dilation (.initial h.1.val, h.2)) →
    Alphabet 8 (shapeMax (initialShape h.1.val))

theorem card_words {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : PopulationHistory K) :
    Fintype.card (Words allocation dilation h) =
      (Contractions.coefficients[shapeMax (initialShape h.1.val)]?.getD 0) ^
        population allocation dilation (.initial h.1.val, h.2) := by
  simp only [Words, Fintype.card_fun, Fintype.card_fin, card_alphabet]

theorem card_words_pos {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : PopulationHistory K) :
    0 < Fintype.card (Words allocation dilation h) := by
  simp only [Words, Fintype.card_fun, Fintype.card_fin]
  exact pow_pos (card_alphabet_pos h.1) _

theorem log_card_words {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (h : PopulationHistory K) :
    Real.log (Fintype.card (Words allocation dilation h) : ℝ) =
      (population allocation dilation (.initial h.1.val, h.2) : ℝ) *
        initialRate (initialShape h.1.val) := by
  simp only [card_words, Nat.cast_pow, Real.log_pow, initialRate]

abbrev ProductWords {K : ℕ} (allocation : Allocation) (dilation : ℕ) :=
  ∀ h : PopulationHistory K, Words allocation dilation h

def volume {K : ℕ} (allocation : Allocation) (dilation : ℕ) : ℕ :=
  Fintype.card (ProductWords (K := K) allocation dilation)

theorem volume_eq_prod {K : ℕ} (allocation : Allocation) (dilation : ℕ) :
    volume (K := K) allocation dilation =
      ∏ h : PopulationHistory K, Fintype.card (Words allocation dilation h) := by
  rw [volume, Fintype.card_pi]

theorem volume_pos {K : ℕ} (allocation : Allocation) (dilation : ℕ) :
    0 < volume (K := K) allocation dilation := by
  rw [volume_eq_prod]
  exact Finset.prod_pos (fun h _ => card_words_pos allocation dilation h)

theorem log_volume {K : ℕ} (allocation : Allocation) (dilation : ℕ) :
    Real.log (volume (K := K) allocation dilation : ℝ) =
      (populationLength (K := K) allocation dilation : ℝ) *
        ∑ h : PopulationHistory K,
          (amount allocation (.initial h.1.val, h.2) : ℝ) *
            initialRate (initialShape h.1.val) := by
  rw [volume_eq_prod, Nat.cast_prod, Real.log_prod
    (fun h _ => Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt (card_words_pos allocation dilation h)))]
  simp only [log_card_words]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  have hc : (population allocation dilation (.initial h.1.val, h.2) : ℝ) =
      (populationLength (K := K) allocation dilation : ℝ) *
        (amount allocation (.initial h.1.val, h.2) : ℝ) := by
    exact_mod_cast population_cast allocation dilation (.initial h.1.val, h.2)
  rw [hc, mul_assoc]

theorem sum_populationHistory_rate {K : ℕ} (allocation : Allocation) :
    (∑ h : PopulationHistory K,
      (amount allocation (.initial h.1.val, h.2) : ℝ) *
        initialRate (initialShape h.1.val)) =
      ∑ h : InitialZero K,
        (initialAmount h.val : ℝ) * initialRate (initialShape h.val) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  dsimp only
  rw [← Finset.sum_mul]
  have hm : (∑ phi : Placement, (amount allocation (.initial h.val, phi) : ℝ)) =
      (initialAmount h.val : ℝ) := by
    exact_mod_cast sum_placement_amount allocation (.initial h.val)
  rw [hm]

theorem log_volume_eq_S0 {K : ℕ} (allocation : Allocation) (dilation : ℕ) :
    Real.log (volume (K := K) allocation dilation : ℝ) =
      (populationLength (K := K) allocation dilation : ℝ) * ((K : ℝ) * S0) := by
  rw [log_volume, sum_populationHistory_rate, initial_zero_history_rate]

theorem normalized_log_volume_eq_S0 {K : ℕ} (allocation : Allocation)
    (dilation : ℕ) (hd : 0 < dilation) :
    Real.log (volume (K := K) allocation dilation : ℝ) /
      populationLength (K := K) allocation dilation = (K : ℝ) * S0 := by
  rw [log_volume_eq_S0]
  have hn : (populationLength (K := K) allocation dilation : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt (AllFieldPopulationCounts.blockLength_pos _ hd))
  exact mul_div_cancel_left₀ _ hn

theorem tendsto_normalized_log_volume {K : ℕ} (allocation : Allocation) :
    Tendsto (fun dilation : ℕ =>
      Real.log (volume (K := K) allocation dilation : ℝ) /
        populationLength (K := K) allocation dilation) atTop (𝓝 ((K : ℝ) * S0)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with dilation hd
  exact (normalized_log_volume_eq_S0 allocation dilation hd).symm

end MatrixMultiplication.AllFieldInitialLeafRates

end

end MatrixAllFields

end OAI
