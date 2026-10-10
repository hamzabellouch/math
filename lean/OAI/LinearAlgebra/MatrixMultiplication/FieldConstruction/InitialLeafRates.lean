import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.TerminalRateFormulas
import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWWordDimensionParameters
import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWWindowedLeaves
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ShapeEncoding

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

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
  rw [volume_eq_prod, Nat.cast_prod, Real.log_prod (s := Finset.univ)
    (f := fun h : PopulationHistory K => (Fintype.card (Words allocation dilation h) : ℝ))
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

end OAI
