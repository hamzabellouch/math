import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWCompleteStatistics
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.LeafRates
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ZeroLeafRateFormula
import Mathlib.SetTheory.Cardinal.Finite

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldZeroLeafRates

open MatrixMultiplication.Foundation Filter AllFieldParameters CWWindowedLeaves CWCompleteStatistics
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

abbrev fourWords (t : Shape) (counts : PairSlot → ℕ) (m : ℕ) :=
  ExactStatisticWords.Words
    (fun w : Alphabet 4 (shapeMax t) => fourStatistic w.val) (fun s => m * counts s)

def twoWords (k : Fin 5) (counts : Fin 6 → ℕ) (m : ℕ) :=
  ExactStatisticWords.Words
    (fun w : Alphabet 2 k.val => twoStatistic w.val) (fun s => m * counts s)

instance twoWordsFintype (k : Fin 5) (counts : Fin 6 → ℕ) (m : ℕ) :
    Fintype (twoWords k counts m) := by
  unfold twoWords
  infer_instance

theorem multiplicity_pos (s : Fin 6) : 0 < AllFieldParameters.multiplicity s := by
  fin_cases s <;> decide

theorem four_supported (t : Shape) (counts : PairSlot → ℕ)
    (hD : 0 < ∑ s, counts s)
    (hlaw : ∀ s, (counts s : ℝ) / (∑ s, counts s : ℕ) =
      (zeroPairLaw t s.1 s.2 : ℝ)) (s : PairSlot) (hs : 0 < counts s) :
    Fintype.card {w : Alphabet 4 (shapeMax t) // fourStatistic w.val = s} =
      AllFieldParameters.multiplicity s.1 * AllFieldParameters.multiplicity s.2 := by
  apply four_fixedWeight_multiplicity
  by_contra hweight
  have hzero := zeroPairLaw_outside_support t s.1 s.2 hweight
  have hpos : (0 : ℝ) < (counts s : ℝ) / (∑ s, counts s : ℕ) :=
    div_pos (by exact_mod_cast hs) (by exact_mod_cast hD)
  rw [hlaw s, hzero, Rat.cast_zero] at hpos
  exact (lt_irrefl 0) hpos

theorem two_supported (d : ℚ) (k : Fin 5) (counts : Fin 6 → ℕ)
    (hD : 0 < ∑ s, counts s)
    (hlaw : ∀ s, (counts s : ℝ) / (∑ s, counts s : ℕ) =
      (statisticLaw d k s : ℝ)) (s : Fin 6) (hs : 0 < counts s) :
    Fintype.card {w : Alphabet 2 k.val // twoStatistic w.val = s} =
      AllFieldParameters.multiplicity s := by
  apply two_fixedWeight_multiplicity
  by_contra hweight
  have hzero := statisticLaw_outside_support d k s hweight
  have hpos : (0 : ℝ) < (counts s : ℝ) / (∑ s, counts s : ℕ) :=
    div_pos (by exact_mod_cast hs) (by exact_mod_cast hD)
  rw [hlaw s, hzero, Rat.cast_zero] at hpos
  exact (lt_irrefl 0) hpos

theorem four_card_pos (t : Shape) (counts : PairSlot → ℕ)
    (hD : 0 < ∑ s, counts s)
    (hlaw : ∀ s, (counts s : ℝ) / (∑ s, counts s : ℕ) =
      (zeroPairLaw t s.1 s.2 : ℝ)) (m : ℕ) :
    0 < Fintype.card (fourWords t counts m) := by
  apply ExactStatisticWords.card_pos_of_supported
    (fun w : Alphabet 4 (shapeMax t) => fourStatistic w.val) (fun s => m * counts s)
    (fun s => AllFieldParameters.multiplicity s.1 * AllFieldParameters.multiplicity s.2)
  · intro s hs
    exact four_supported t counts hD hlaw s (Nat.pos_of_mul_pos_left hs)
  · intro s _
    exact Nat.mul_pos (multiplicity_pos s.1) (multiplicity_pos s.2)

theorem two_card_pos (d : ℚ) (k : Fin 5) (counts : Fin 6 → ℕ)
    (hD : 0 < ∑ s, counts s)
    (hlaw : ∀ s, (counts s : ℝ) / (∑ s, counts s : ℕ) =
      (statisticLaw d k s : ℝ)) (m : ℕ) :
    0 < Fintype.card (twoWords k counts m) := by
  have h := ExactStatisticWords.card_pos_of_supported
    (fun w : Alphabet 2 k.val => twoStatistic w.val) (fun s => m * counts s)
    AllFieldParameters.multiplicity
    (fun s hs => two_supported d k counts hD hlaw s (Nat.pos_of_mul_pos_left hs))
    (fun s _ => multiplicity_pos s)
  rw [Fintype.card_eq_nat_card] at h ⊢
  exact h

theorem four_tendsto_log_card (t : Shape) (counts : PairSlot → ℕ)
    (hD : 0 < ∑ s, counts s)
    (hlaw : ∀ s, (counts s : ℝ) / (∑ s, counts s : ℕ) =
      (zeroPairLaw t s.1 s.2 : ℝ)) :
    Tendsto (fun m : ℕ => Real.log (Fintype.card (fourWords t counts m) : ℝ) /
      ((m : ℝ) * (∑ s, counts s : ℕ))) atTop (𝓝 (fourRate t)) := by
  have h := LeafRates.tendsto_log_card_supported
    (fun w : Alphabet 4 (shapeMax t) => fourStatistic w.val) counts
    (fun s => AllFieldParameters.multiplicity s.1 * AllFieldParameters.multiplicity s.2)
    (four_supported t counts hD hlaw)
    (fun s => Nat.mul_pos (multiplicity_pos s.1) (multiplicity_pos s.2)) hD
  simpa only [fourWords, hlaw, fourRate] using h

theorem two_tendsto_log_card (d : ℚ) (k : Fin 5) (counts : Fin 6 → ℕ)
    (hD : 0 < ∑ s, counts s)
    (hlaw : ∀ s, (counts s : ℝ) / (∑ s, counts s : ℕ) =
      (statisticLaw d k s : ℝ)) :
    Tendsto (fun m : ℕ => Real.log (Fintype.card (twoWords k counts m) : ℝ) /
      ((m : ℝ) * (∑ s, counts s : ℕ))) atTop (𝓝 (statisticRate d k)) := by
  have h := LeafRates.tendsto_log_card_supported
    (fun w : Alphabet 2 k.val => twoStatistic w.val) counts AllFieldParameters.multiplicity
    (two_supported d k counts hD hlaw) multiplicity_pos hD
  simp only [Fintype.card_eq_nat_card] at h ⊢
  simpa only [twoWords, hlaw, statisticRate] using h

end MatrixMultiplication.AllFieldZeroLeafRates

end

end OAI
