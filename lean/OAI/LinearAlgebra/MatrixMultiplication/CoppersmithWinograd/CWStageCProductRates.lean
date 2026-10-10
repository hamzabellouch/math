import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWStageCProducts
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.StageCLaw
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Populations
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.CWStageCProducts

attribute [local instance] Classical.propDecidable Classical.decEq

theorem card_positions (counts : Fin 4 → ℕ) :
    Fintype.card (Positions counts) = totalCount counts := by
  simp [Positions, Fintype.card_sigma, Fin.sum_univ_succ, totalCount,
    singleCount, crossCount, Nat.add_assoc]

theorem card_rowWords (s : Fin 3) (counts : Fin 4 → ℕ) :
    Fintype.card (RowWords s counts) =
      5 ^ (if s = 1 then singleCount counts else crossCount counts) := by
  rw [Fintype.card_eq_nat_card, Nat.card_pi, Fintype.prod_sigma]
  fin_cases s <;>
    simp [Fin.prod_univ_succ, Row, SmallRow, SmallInner, singleCount, crossCount,
      pow_add, Nat.card_fin, -Nat.card_eq_fintype_card]

theorem card_middleWords (s : Fin 3) (counts : Fin 4 → ℕ) :
    Fintype.card (MiddleWords s counts) =
      5 ^ (if s = 2 then singleCount counts else crossCount counts) := by
  rw [Fintype.card_eq_nat_card, Nat.card_pi, Fintype.prod_sigma]
  fin_cases s <;>
    simp [Fin.prod_univ_succ, Middle, SmallRow, SmallInner, singleCount, crossCount,
      pow_add, Nat.card_fin, -Nat.card_eq_fintype_card]

theorem card_columnWords (s : Fin 3) (counts : Fin 4 → ℕ) :
    Fintype.card (ColumnWords s counts) =
      5 ^ (if s = 0 then singleCount counts else crossCount counts) := by
  rw [Fintype.card_eq_nat_card, Nat.card_pi, Fintype.prod_sigma]
  fin_cases s <;>
    simp [Fin.prod_univ_succ, Column, SmallRow, SmallInner, singleCount, crossCount,
      pow_add, Nat.card_fin, -Nat.card_eq_fintype_card]

def volume (s : Fin 3) (counts : Fin 4 → ℕ) : ℕ :=
  Fintype.card (RowWords s counts) * Fintype.card (MiddleWords s counts) *
    Fintype.card (ColumnWords s counts)

theorem volume_eq (s : Fin 3) (counts : Fin 4 → ℕ) :
    volume s counts = 5 ^ (singleCount counts + 2 * crossCount counts) := by
  rw [volume, card_rowWords, card_middleWords, card_columnWords]
  fin_cases s <;> simp [pow_add, two_mul] <;> ring

theorem volume_pos (s : Fin 3) (counts : Fin 4 → ℕ) : 0 < volume s counts := by
  rw [volume_eq]
  positivity

theorem log_volume (s : Fin 3) (counts : Fin 4 → ℕ) :
    Real.log (volume s counts : ℝ) =
      ((singleCount counts : ℝ) + 2 * crossCount counts) * Real.log 5 := by
  rw [volume_eq]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_add, Nat.cast_mul]

theorem normalized_log_volume (s : Fin 3) (counts : Fin 4 → ℕ)
    (hpos : 0 < totalCount counts) :
    Real.log (volume s counts : ℝ) / totalCount counts =
      (2 - (singleCount counts : ℝ) / totalCount counts) * Real.log 5 := by
  have hn : (totalCount counts : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos)
  have ht : (totalCount counts : ℝ) = singleCount counts + (crossCount counts : ℝ) := by
    simp [totalCount]
  rw [log_volume, mul_div_right_comm]
  congr 1
  field_simp [hn]
  rw [ht]
  ring

theorem totalCount_of_atom_counts (counts : Fin 4 → ℕ)
    (t u : AllFieldParameters.Shape) (n : ℕ)
    (hc : ∀ i, (counts i : ℚ) = (n : ℚ) * AllFieldHistory.stageCWeight t u i) :
    totalCount counts = n := by
  apply Nat.cast_injective (R := ℚ)
  calc
    (totalCount counts : ℚ) = ∑ i, (counts i : ℚ) := by
      simp [totalCount, singleCount, crossCount, Fin.sum_univ_succ, add_assoc]
    _ = n := by
      simp only [hc, ← Finset.mul_sum, AllFieldHistory.stageCWeight_normalized, mul_one]

theorem log_volume_of_atom_counts (s : Fin 3) (counts : Fin 4 → ℕ)
    (t u : AllFieldParameters.Shape) (n : ℕ)
    (hc : ∀ i, (counts i : ℚ) = (n : ℚ) * AllFieldHistory.stageCWeight t u i) :
    Real.log (volume s counts : ℝ) =
      (n : ℝ) * (2 - (AllFieldParameters.binaryParameter t u : ℝ)) * Real.log 5 := by
  have hs : (singleCount counts : ℚ) = (n : ℚ) * AllFieldParameters.binaryParameter t u := by
    simp only [singleCount, Nat.cast_add, hc, ← mul_add,
      AllFieldHistory.stageCWeight_single]
  have hx : (crossCount counts : ℚ) =
      (n : ℚ) * (1 - AllFieldParameters.binaryParameter t u) := by
    simp only [crossCount, Nat.cast_add, hc, ← mul_add,
      AllFieldHistory.stageCWeight_cross]
  have hsr : (singleCount counts : ℝ) =
      (n : ℝ) * (AllFieldParameters.binaryParameter t u : ℝ) := by exact_mod_cast hs
  have hxr : (crossCount counts : ℝ) =
      (n : ℝ) * (1 - (AllFieldParameters.binaryParameter t u : ℝ)) := by exact_mod_cast hx
  rw [log_volume, hsr, hxr]
  ring

theorem normalized_log_volume_of_atom_counts (s : Fin 3) (counts : Fin 4 → ℕ)
    (t u : AllFieldParameters.Shape) (n : ℕ) (hn : 0 < n)
    (hc : ∀ i, (counts i : ℚ) = (n : ℚ) * AllFieldHistory.stageCWeight t u i) :
    Real.log (volume s counts : ℝ) / totalCount counts =
      (2 - (AllFieldParameters.binaryParameter t u : ℝ)) * Real.log 5 := by
  rw [log_volume_of_atom_counts s counts t u n hc, totalCount_of_atom_counts counts t u n hc]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  field_simp [hn']

variable {H : Type*} [Fintype H]

abbrev HistoryRowWords (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :=
  ∀ h, RowWords (side h) (counts h)
abbrev HistoryMiddleWords (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :=
  ∀ h, MiddleWords (side h) (counts h)
abbrev HistoryColumnWords (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :=
  ∀ h, ColumnWords (side h) (counts h)

theorem card_historyRowWords (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :
    Fintype.card (HistoryRowWords side counts) =
      5 ^ ∑ h, (if side h = 1 then singleCount (counts h) else crossCount (counts h)) := by
  rw [Fintype.card_pi]
  simp only [card_rowWords]
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem card_historyMiddleWords (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :
    Fintype.card (HistoryMiddleWords side counts) =
      5 ^ ∑ h, (if side h = 2 then singleCount (counts h) else crossCount (counts h)) := by
  rw [Fintype.card_pi]
  simp only [card_middleWords]
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem card_historyColumnWords (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :
    Fintype.card (HistoryColumnWords side counts) =
      5 ^ ∑ h, (if side h = 0 then singleCount (counts h) else crossCount (counts h)) := by
  rw [Fintype.card_pi]
  simp only [card_columnWords]
  exact Finset.prod_pow_eq_pow_sum _ _ _

def historyVolume (side : H → Fin 3) (counts : H → Fin 4 → ℕ) : ℕ :=
  Fintype.card (HistoryRowWords side counts) *
    Fintype.card (HistoryMiddleWords side counts) *
      Fintype.card (HistoryColumnWords side counts)

theorem historyVolume_eq_prod (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :
    historyVolume side counts = ∏ h, volume (side h) (counts h) := by
  simp only [historyVolume, HistoryRowWords, HistoryMiddleWords, HistoryColumnWords,
    Fintype.card_pi, volume, Finset.prod_mul_distrib]

theorem historyVolume_eq (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :
    historyVolume side counts =
      5 ^ ∑ h, (singleCount (counts h) + 2 * crossCount (counts h)) := by
  rw [historyVolume_eq_prod]
  simp only [volume_eq]
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem log_historyVolume (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :
    Real.log (historyVolume side counts : ℝ) =
      ∑ h, ((singleCount (counts h) : ℝ) + 2 * crossCount (counts h)) * Real.log 5 := by
  rw [historyVolume_eq]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_sum,
    Nat.cast_add, Nat.cast_mul, Finset.sum_mul]

theorem log_historyVolume_of_mass_counts (side : H → Fin 3)
    (counts : H → Fin 4 → ℕ) (t u : H → AllFieldParameters.Shape)
    (mass : H → ℚ) (N : ℕ)
    (hc : ∀ h i, (counts h i : ℚ) =
      (N : ℚ) * mass h * AllFieldHistory.stageCWeight (t h) (u h) i) :
    Real.log (historyVolume side counts : ℝ) =
      (N : ℝ) * ∑ h, (mass h : ℝ) *
        (2 - (AllFieldParameters.binaryParameter (t h) (u h) : ℝ)) * Real.log 5 := by
  have hs (h : H) : (singleCount (counts h) : ℚ) =
      (N : ℚ) * mass h * AllFieldParameters.binaryParameter (t h) (u h) := by
    simp only [singleCount, Nat.cast_add, hc, ← mul_add,
      AllFieldHistory.stageCWeight_single]
  have hx (h : H) : (crossCount (counts h) : ℚ) =
      (N : ℚ) * mass h * (1 - AllFieldParameters.binaryParameter (t h) (u h)) := by
    simp only [crossCount, Nat.cast_add, hc, ← mul_add,
      AllFieldHistory.stageCWeight_cross]
  rw [log_historyVolume, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  have hsr : (singleCount (counts h) : ℝ) =
      (N : ℝ) * (mass h : ℝ) * (AllFieldParameters.binaryParameter (t h) (u h) : ℝ) := by
    exact_mod_cast hs h
  have hxr : (crossCount (counts h) : ℝ) =
      (N : ℝ) * (mass h : ℝ) * (1 - (AllFieldParameters.binaryParameter (t h) (u h) : ℝ)) := by
    exact_mod_cast hx h
  rw [hsr, hxr]
  ring

theorem normalized_log_historyVolume_of_mass_counts (side : H → Fin 3)
    (counts : H → Fin 4 → ℕ) (t u : H → AllFieldParameters.Shape)
    (mass : H → ℚ) (N : ℕ) (hN : 0 < N)
    (hc : ∀ h i, (counts h i : ℚ) =
      (N : ℚ) * mass h * AllFieldHistory.stageCWeight (t h) (u h) i) :
    Real.log (historyVolume side counts : ℝ) / N =
      ∑ h, (mass h : ℝ) *
        (2 - (AllFieldParameters.binaryParameter (t h) (u h) : ℝ)) * Real.log 5 := by
  rw [log_historyVolume_of_mass_counts side counts t u mass N hc]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  exact mul_div_cancel_left₀ _ hn

abbrev PopulationHistory (K : ℕ) := AllFieldHistory.PartC K × AllFieldHistory.Placement

def populationSide {K : ℕ} (h : PopulationHistory K) : Fin 3 :=
  h.2 (AllFieldHistory.stageCDistinguished (AllFieldHistory.cShapeParent h.1))

def populationAtomCounts {K : ℕ} (allocation : AllFieldHistory.Allocation)
    (dilation : ℕ) (h : PopulationHistory K) (i : Fin 4) : ℕ :=
  AllFieldHistory.population allocation dilation (.afterC (h.1, i, false), h.2)

theorem populationAtomCounts_mass {K : ℕ} (allocation : AllFieldHistory.Allocation)
    (dilation : ℕ) (h : PopulationHistory K) (i : Fin 4) :
    (populationAtomCounts allocation dilation h i : ℚ) =
      (AllFieldHistory.populationLength (K := K) allocation dilation : ℚ) *
        AllFieldHistory.amount allocation (.partC h.1, h.2) *
          AllFieldHistory.stageCWeight (AllFieldHistory.cParameterParent h.1)
            (AllFieldHistory.cShapeParent h.1) i := by
  rw [populationAtomCounts, AllFieldHistory.population_cast]
  simp only [AllFieldHistory.amount, AllFieldHistory.canonicalAmount,
    AllFieldHistory.cAmount]
  ring

theorem populationAtomCounts_parent {K : ℕ} (allocation : AllFieldHistory.Allocation)
    (dilation : ℕ) (h : PopulationHistory K) (i : Fin 4) :
    (populationAtomCounts allocation dilation h i : ℚ) =
      (AllFieldHistory.population allocation dilation (.partC h.1, h.2) : ℚ) *
        AllFieldHistory.stageCWeight (AllFieldHistory.cParameterParent h.1)
          (AllFieldHistory.cShapeParent h.1) i := by
  rw [populationAtomCounts_mass, AllFieldHistory.population_cast]

theorem populationAtomCounts_total {K : ℕ} (allocation : AllFieldHistory.Allocation)
    (dilation : ℕ) (h : PopulationHistory K) :
    totalCount (populationAtomCounts allocation dilation h) =
      AllFieldHistory.population allocation dilation (.partC h.1, h.2) := by
  simpa [totalCount, singleCount, crossCount, populationAtomCounts,
    Fin.sum_univ_succ, Nat.add_assoc] using
    AllFieldHistory.c_population_transition allocation dilation h.1 false h.2

theorem log_population_historyVolume {K : ℕ} (allocation : AllFieldHistory.Allocation)
    (dilation : ℕ) (side : PopulationHistory K → Fin 3) :
    Real.log (historyVolume side (populationAtomCounts allocation dilation) : ℝ) =
      (AllFieldHistory.populationLength (K := K) allocation dilation : ℝ) *
        ∑ h : PopulationHistory K,
          (AllFieldHistory.amount allocation (.partC h.1, h.2) : ℝ) *
            (2 - (AllFieldParameters.binaryParameter
              (AllFieldHistory.cParameterParent h.1)
              (AllFieldHistory.cShapeParent h.1) : ℝ)) * Real.log 5 := by
  exact log_historyVolume_of_mass_counts side (populationAtomCounts allocation dilation)
    (fun h => AllFieldHistory.cParameterParent h.1)
    (fun h => AllFieldHistory.cShapeParent h.1)
    (fun h => AllFieldHistory.amount allocation (.partC h.1, h.2))
    (AllFieldHistory.populationLength (K := K) allocation dilation)
    (populationAtomCounts_mass allocation dilation)

theorem normalized_log_population_historyVolume {K : ℕ}
    (allocation : AllFieldHistory.Allocation) (dilation : ℕ) (hd : 0 < dilation)
    (side : PopulationHistory K → Fin 3) :
    Real.log (historyVolume side (populationAtomCounts allocation dilation) : ℝ) /
        AllFieldHistory.populationLength (K := K) allocation dilation =
      ∑ h : PopulationHistory K,
        (AllFieldHistory.amount allocation (.partC h.1, h.2) : ℝ) *
          (2 - (AllFieldParameters.binaryParameter
            (AllFieldHistory.cParameterParent h.1)
            (AllFieldHistory.cShapeParent h.1) : ℝ)) * Real.log 5 := by
  exact normalized_log_historyVolume_of_mass_counts side
    (populationAtomCounts allocation dilation)
    (fun h => AllFieldHistory.cParameterParent h.1)
    (fun h => AllFieldHistory.cShapeParent h.1)
    (fun h => AllFieldHistory.amount allocation (.partC h.1, h.2))
    (AllFieldHistory.populationLength (K := K) allocation dilation)
    (AllFieldPopulationCounts.blockLength_pos _ hd)
    (populationAtomCounts_mass allocation dilation)

def populationVolume {K : ℕ} (allocation : AllFieldHistory.Allocation)
    (dilation : ℕ) : ℕ :=
  historyVolume (populationSide (K := K)) (populationAtomCounts allocation dilation)

theorem log_populationVolume {K : ℕ} (allocation : AllFieldHistory.Allocation)
    (dilation : ℕ) :
    Real.log (populationVolume (K := K) allocation dilation : ℝ) =
      (AllFieldHistory.populationLength (K := K) allocation dilation : ℝ) *
        ∑ h : PopulationHistory K,
          (AllFieldHistory.amount allocation (.partC h.1, h.2) : ℝ) *
            (2 - (AllFieldParameters.binaryParameter
              (AllFieldHistory.cParameterParent h.1)
              (AllFieldHistory.cShapeParent h.1) : ℝ)) * Real.log 5 :=
  log_population_historyVolume allocation dilation populationSide

theorem normalized_log_populationVolume {K : ℕ}
    (allocation : AllFieldHistory.Allocation) (dilation : ℕ) (hd : 0 < dilation) :
    Real.log (populationVolume (K := K) allocation dilation : ℝ) /
        AllFieldHistory.populationLength (K := K) allocation dilation =
      ∑ h : PopulationHistory K,
        (AllFieldHistory.amount allocation (.partC h.1, h.2) : ℝ) *
          (2 - (AllFieldParameters.binaryParameter
            (AllFieldHistory.cParameterParent h.1)
            (AllFieldHistory.cShapeParent h.1) : ℝ)) * Real.log 5 :=
  normalized_log_population_historyVolume allocation dilation hd populationSide

end MatrixMultiplication.CWStageCProducts

end

end OAI
