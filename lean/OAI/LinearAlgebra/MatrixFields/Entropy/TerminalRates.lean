import Mathlib
import OAI.LinearAlgebra.MatrixFields.Histories.ZeroHistorySums
import OAI.LinearAlgebra.MatrixFields.Parameters.TerminalPopulations

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldTerminalRates

open AllFieldHistory AllFieldParameters AllFieldTerminalStatisticLaws
open AllFieldZeroLeafRates AllFieldZeroHistorySums Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

variable {K : ℕ}

def statisticCounts (allocation : Allocation) (h : TerminalZero K) : Slot h → ℕ :=
  AllFieldTerminalPopulations.count allocation history law 1 h

def terminalDilation (K : ℕ) (m : ℕ) : ℕ :=
  AllFieldTerminalPopulations.dilation (law (K := K)) m

def terminalLength (allocation : Allocation) (K : ℕ) (m : ℕ) : ℕ :=
  populationLength (K := K) allocation (terminalDilation K m)

theorem terminalDilation_pos {m : ℕ} (hm : 0 < m) :
    0 < terminalDilation K m :=
  AllFieldTerminalPopulations.dilation_pos law hm

theorem terminalLength_pos (allocation : Allocation) {m : ℕ} (hm : 0 < m) :
    0 < terminalLength allocation K m :=
  AllFieldPopulationCounts.blockLength_pos _ (terminalDilation_pos hm)

theorem terminalLength_mul_one (allocation : Allocation) (m : ℕ) :
    terminalLength allocation K m = m * terminalLength allocation K 1 := by
  simp only [terminalLength, terminalDilation, AllFieldTerminalPopulations.dilation,
    populationLength, AllFieldPopulationCounts.blockLength, one_mul, mul_assoc]

theorem statisticCounts_pos (allocation : Allocation) (h : TerminalZero K) :
    0 < ∑ s, statisticCounts allocation h s :=
  AllFieldTerminalPopulations.sum_count_pos allocation history law law_nonneg law_total
    (by decide) h (history_amount_pos allocation h)

theorem statisticCounts_ratio (allocation : Allocation) (h : TerminalZero K) (s : Slot h) :
    (statisticCounts allocation h s : ℝ) /
      (∑ s, statisticCounts allocation h s : ℕ) = (law h s : ℝ) :=
  AllFieldTerminalPopulations.count_ratio_real allocation history law law_nonneg law_total
    (by decide) h (history_amount_pos allocation h) s

theorem statisticCounts_sum_inl (allocation : Allocation) (h : AZero K) :
    (∑ s : Slot (.inl h), statisticCounts allocation (.inl h) s) =
      ∑ s : PairSlot, statisticCounts allocation (.inl h) s := by
  exact Fintype.sum_equiv (Equiv.refl _) _ _ (fun _ => rfl)

theorem statisticCounts_sum_inr (allocation : Allocation) (h : BZero K) :
    (∑ s : Slot (.inr h), statisticCounts allocation (.inr h) s) =
      ∑ s : Fin 6, statisticCounts allocation (.inr h) s := by
  exact Fintype.sum_equiv (Equiv.refl _) _ _ (fun _ => rfl)

theorem statisticCounts_sum (allocation : Allocation) (h : TerminalZero K) :
    (∑ s, statisticCounts allocation h s) =
      population allocation (terminalDilation K 1) (history h) :=
  AllFieldTerminalPopulations.sum_count allocation history law law_nonneg law_total 1 h

theorem statisticCounts_repeat (allocation : Allocation) (m : ℕ)
    (h : TerminalZero K) (s : Slot h) :
    m * statisticCounts allocation h s =
      AllFieldTerminalPopulations.count allocation history law m h s :=
  (AllFieldTerminalPopulations.count_mul_one allocation history law m h s).symm

theorem statisticCounts_repeat_sum (allocation : Allocation) (m : ℕ)
    (h : TerminalZero K) :
    (∑ s, m * statisticCounts allocation h s) =
      population allocation (terminalDilation K m) (history h) := by
  simp only [statisticCounts_repeat]
  exact AllFieldTerminalPopulations.sum_count allocation history law law_nonneg law_total m h

theorem statisticCounts_sum_cast (allocation : Allocation) (h : TerminalZero K) :
    ((∑ s, statisticCounts allocation h s : ℕ) : ℝ) =
      (terminalLength allocation K 1 : ℝ) * (amount allocation (history h) : ℝ) := by
  rw [statisticCounts_sum]
  exact_mod_cast population_cast allocation (terminalDilation K 1) (history h)

def ZeroWords (allocation : Allocation) (m : ℕ) : TerminalZero K → Type
  | .inl h => fourWords (aShape h.1.val) (statisticCounts allocation (.inl h)) m
  | .inr h => twoWords (bWeight h) (statisticCounts allocation (.inr h)) m

local instance terminalTwoWordsFintype (allocation : Allocation) (m : ℕ) (h : BZero K) :
    Fintype (twoWords (bWeight h) (statisticCounts allocation (.inr h)) m) :=
  twoWordsFintype _ _ _

instance zeroWordsFintype (allocation : Allocation) (m : ℕ) (h : TerminalZero K) :
    Fintype (ZeroWords allocation m h) := by
  cases h <;> dsimp [ZeroWords] <;> infer_instance

theorem zeroWords_card_inl (allocation : Allocation) (m : ℕ) (h : AZero K) :
    Fintype.card (ZeroWords allocation m (.inl h)) =
      Fintype.card (fourWords (aShape h.1.val) (statisticCounts allocation (.inl h)) m) := by
  exact Fintype.card_congr (Equiv.refl _)

theorem zeroWords_card_inr (allocation : Allocation) (m : ℕ) (h : BZero K) :
    Fintype.card (ZeroWords allocation m (.inr h)) =
      Fintype.card (twoWords (bWeight h) (statisticCounts allocation (.inr h)) m) := by
  exact Fintype.card_congr (Equiv.refl _)

theorem zeroWords_card_pos (allocation : Allocation) (m : ℕ) (h : TerminalZero K) :
    0 < Fintype.card (ZeroWords allocation m h) := by
  cases h with
  | inl h =>
      rw [zeroWords_card_inl]
      exact four_card_pos (aShape h.1.val) (statisticCounts allocation (.inl h))
        (by simpa only [statisticCounts_sum_inl] using statisticCounts_pos allocation (.inl h))
        (by
          intro slot
          simpa only [statisticCounts_sum_inl, law_inl] using
            statisticCounts_ratio allocation (.inl h) slot) m
  | inr h =>
      rw [zeroWords_card_inr]
      exact two_card_pos (binaryParameter (bParent h) (bShape h.1.val))
        (bWeight h) (statisticCounts allocation (.inr h))
        (by simpa only [statisticCounts_sum_inr] using statisticCounts_pos allocation (.inr h))
        (by
          intro slot
          simpa only [statisticCounts_sum_inr, law_inr] using
            statisticCounts_ratio allocation (.inr h) slot) m

theorem tendsto_zeroWords_local (allocation : Allocation) (h : TerminalZero K) :
    Tendsto (fun m : ℕ => Real.log (Fintype.card (ZeroWords allocation m h) : ℝ) /
      ((m : ℝ) * (∑ s, statisticCounts allocation h s : ℕ))) atTop
      (𝓝 (zeroRate h)) := by
  cases h with
  | inl h =>
      simp only [zeroWords_card_inl, zeroRate, statisticCounts_sum_inl]
      simpa only [Fintype.card_eq_nat_card] using
        four_tendsto_log_card (aShape h.1.val) (statisticCounts allocation (.inl h))
        (by simpa only [statisticCounts_sum_inl] using statisticCounts_pos allocation (.inl h))
        (by
          intro slot
          simpa only [statisticCounts_sum_inl, law_inl] using
            statisticCounts_ratio allocation (.inl h) slot)
  | inr h =>
      simp only [zeroWords_card_inr, zeroRate, statisticCounts_sum_inr]
      simpa only [Fintype.card_eq_nat_card] using
        two_tendsto_log_card (binaryParameter (bParent h) (bShape h.1.val))
        (bWeight h) (statisticCounts allocation (.inr h))
        (by simpa only [statisticCounts_sum_inr] using statisticCounts_pos allocation (.inr h))
        (by
          intro slot
          simpa only [statisticCounts_sum_inr, law_inr] using
            statisticCounts_ratio allocation (.inr h) slot)

theorem tendsto_zeroWords (hK : 0 < K) (allocation : Allocation) (h : TerminalZero K) :
    Tendsto (fun m : ℕ => Real.log (Fintype.card (ZeroWords allocation m h) : ℝ) /
      ((K : ℝ) * terminalLength allocation K m)) atTop
      (𝓝 ((amount allocation (history h) : ℝ) * zeroRate h / K)) := by
  have ht := (tendsto_zeroWords_local allocation h).mul_const
    ((amount allocation (history h) : ℝ) / K)
  have hr : zeroRate h * ((amount allocation (history h) : ℝ) / K) =
      (amount allocation (history h) : ℝ) * zeroRate h / K := by ring
  rw [hr] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hk' : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  have hn' : (terminalLength allocation K 1 : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (terminalLength_pos allocation (K := K) (m := 1) (by decide))
  have ha' : (amount allocation (history h) : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt (history_amount_pos allocation h)
  rw [terminalLength_mul_one, Nat.cast_mul, statisticCounts_sum_cast]
  field_simp [hm', hk', hn', ha']

def zeroVolume (allocation : Allocation) (m : ℕ) : ℕ :=
  Fintype.card (∀ h : TerminalZero K, ZeroWords allocation m h)

theorem zeroVolume_pos (allocation : Allocation) (m : ℕ) :
    0 < zeroVolume (K := K) allocation m := by
  simp only [zeroVolume, Fintype.card_pi]
  exact Finset.prod_pos fun h _ => zeroWords_card_pos allocation m h

theorem log_zeroVolume (allocation : Allocation) (m : ℕ) :
    Real.log (zeroVolume (K := K) allocation m : ℝ) =
      ∑ h : TerminalZero K, Real.log (Fintype.card (ZeroWords allocation m h) : ℝ) := by
  rw [zeroVolume, Fintype.card_pi, Nat.cast_prod]
  exact Real.log_prod (fun h _ => by
    exact_mod_cast Nat.ne_of_gt (zeroWords_card_pos allocation m h))

theorem tendsto_zeroVolume (hK : 0 < K) (allocation : Allocation) :
    Tendsto (fun m : ℕ => Real.log (zeroVolume (K := K) allocation m : ℝ) /
      ((K : ℝ) * terminalLength allocation K m)) atTop
      (𝓝 (S1 + S2 - AllFieldStageCTerminalRates.interiorS2)) := by
  have ht := tendsto_finsetSum Finset.univ
    (fun h _ => tendsto_zeroWords hK allocation h)
  have hr : (∑ h : TerminalZero K, (amount allocation (history h) : ℝ) * zeroRate h / K) =
      S1 + S2 - AllFieldStageCTerminalRates.interiorS2 := by
    rw [← Finset.sum_div, zero_history_sum K allocation]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast Nat.ne_of_gt hK)
  rw [hr] at ht
  convert ht using 1
  ext m
  rw [log_zeroVolume, Finset.sum_div]

def terminalVolume (allocation : Allocation) (m : ℕ) : ℕ :=
  AllFieldInitialLeafRates.volume (K := K) allocation (terminalDilation K m) *
    zeroVolume (K := K) allocation m *
      CWStageCProducts.populationVolume (K := K) allocation (terminalDilation K m)

theorem stageCVolume_pos (allocation : Allocation) (dilation : ℕ) :
    0 < CWStageCProducts.populationVolume (K := K) allocation dilation := by
  unfold CWStageCProducts.populationVolume
  rw [CWStageCProducts.historyVolume_eq_prod]
  exact Finset.prod_pos fun h _ => CWStageCProducts.volume_pos _ _

theorem terminalVolume_pos (allocation : Allocation) (m : ℕ) :
    0 < terminalVolume (K := K) allocation m := by
  exact Nat.mul_pos
    (Nat.mul_pos (AllFieldInitialLeafRates.volume_pos allocation _)
      (zeroVolume_pos allocation m)) (stageCVolume_pos allocation _)

theorem log_terminalVolume (allocation : Allocation) (m : ℕ) :
    Real.log (terminalVolume (K := K) allocation m : ℝ) =
      Real.log (AllFieldInitialLeafRates.volume (K := K) allocation
        (terminalDilation K m) : ℝ) +
      Real.log (zeroVolume (K := K) allocation m : ℝ) +
      Real.log (CWStageCProducts.populationVolume (K := K) allocation
        (terminalDilation K m) : ℝ) := by
  have hI : (AllFieldInitialLeafRates.volume (K := K) allocation
      (terminalDilation K m) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (AllFieldInitialLeafRates.volume_pos allocation _)
  have hZ : (zeroVolume (K := K) allocation m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (zeroVolume_pos allocation m)
  have hC : (CWStageCProducts.populationVolume (K := K) allocation
      (terminalDilation K m) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (stageCVolume_pos allocation _)
  simp only [terminalVolume, Nat.cast_mul, Real.log_mul (mul_ne_zero hI hZ) hC,
    Real.log_mul hI hZ]

theorem normalized_log_initialVolume (hK : 0 < K) (allocation : Allocation)
    {m : ℕ} (hm : 0 < m) :
    Real.log (AllFieldInitialLeafRates.volume (K := K) allocation
      (terminalDilation K m) : ℝ) / ((K : ℝ) * terminalLength allocation K m) = S0 := by
  rw [AllFieldInitialLeafRates.log_volume_eq_S0]
  change (terminalLength allocation K m : ℝ) * ((K : ℝ) * S0) /
    ((K : ℝ) * terminalLength allocation K m) = S0
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  have hn : (terminalLength allocation K m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (terminalLength_pos allocation hm)
  field_simp [hk, hn]

theorem normalized_log_stageCVolume (hK : 0 < K) (allocation : Allocation)
    {m : ℕ} (hm : 0 < m) :
    Real.log (CWStageCProducts.populationVolume (K := K) allocation
      (terminalDilation K m) : ℝ) / ((K : ℝ) * terminalLength allocation K m) =
        AllFieldStageCTerminalRates.interiorS2 :=
  AllFieldStageCTerminalRates.normalized_log_populationVolume_eq_interior
    hK allocation _ (terminalDilation_pos hm)

theorem tendsto_terminalVolume (hK : 0 < K) (allocation : Allocation) :
    Tendsto (fun m : ℕ => Real.log (terminalVolume (K := K) allocation m : ℝ) /
      ((K : ℝ) * terminalLength allocation K m)) atTop (𝓝 S) := by
  have hI : Tendsto (fun m : ℕ =>
      Real.log (AllFieldInitialLeafRates.volume (K := K) allocation
        (terminalDilation K m) : ℝ) / ((K : ℝ) * terminalLength allocation K m))
        atTop (𝓝 S0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    exact (normalized_log_initialVolume hK allocation hm).symm
  have hC : Tendsto (fun m : ℕ =>
      Real.log (CWStageCProducts.populationVolume (K := K) allocation
        (terminalDilation K m) : ℝ) / ((K : ℝ) * terminalLength allocation K m))
        atTop (𝓝 AllFieldStageCTerminalRates.interiorS2) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    exact (normalized_log_stageCVolume hK allocation hm).symm
  have ht := (hI.add (tendsto_zeroVolume hK allocation)).add hC
  have hr : S0 + (S1 + S2 - AllFieldStageCTerminalRates.interiorS2) +
      AllFieldStageCTerminalRates.interiorS2 = S := by unfold S; ring
  rw [hr] at ht
  convert ht using 1
  ext m
  rw [log_terminalVolume, add_div, add_div]

end MatrixMultiplication.AllFieldTerminalRates

end
end

end MatrixAllFields

end OAI
