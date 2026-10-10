import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightScaleCenters
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightScaleNumerics

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open HistoryProductWindows Construction InitialCoordinatesTemplate Conclusion

def sourceScaleConstant (Bs BD Bz : ℝ) (k : ℕ) : ℝ :=
  2 * scaleLinearConstant Bs BD Bz k + 3 + (2 : ℝ)^k * (18 + 10 * (k : ℝ))

theorem sourceScaleConstant_pos (Bs BD Bz : ℝ) (k : ℕ) :
    0 < sourceScaleConstant Bs BD Bz k := by
  have hc := scaleLinearConstant_pos Bs BD Bz k
  unfold sourceScaleConstant
  positivity

theorem sourceCancellationExponent_le_linear (Bs BD Bz : ℝ) (b k : ℕ) (L tb J : ℝ)
    (center : ℕ → ℝ) (hm : 1 ≤ bulkSize k L) {j : ℕ} (hj : j < k)
    (htop : |(∑ h, ∑ i, topCenters b center h i) - (J - 2 * tb)| ≤ 2)
    (htypes : ∀ i < k, |typeCenter b i center - nominalWeight k J (stepGap BD Bz k L) i| ≤ 2) :
    sourceCancellationExponent (Conclusion.frequencyBound Bs BD Bz k L) b k tb center j ≤
      sourceScaleConstant Bs BD Bz k * (bulkSize k L : ℝ) := by
  have hnom := sourceCancellationExponent_le_nominal
    (Conclusion.frequencyBound Bs BD Bz k L) b k tb J (stepGap BD Bz k L) center hj htop htypes
  have hfreq := log_frequencyBound_add_one_le_linear Bs BD Bz k L hm hj.le
  have hstep := stepGap_le_linear Bs BD Bz k L hj
  have hwidth := nominal_widths_le k hj.le
  have hm' : (1 : ℝ) ≤ bulkSize k L := by exact_mod_cast hm
  have hW : 0 ≤ 2 + (2 : ℝ)^k * (18 + 10 * (k : ℝ)) := by positivity
  have hWm := mul_le_mul_of_nonneg_left hm' hW
  unfold sourceScaleConstant
  nlinarith

theorem sourceCancellationBound_le_exp_linear (Bs BD Bz : ℝ) (b k : ℕ) (L tb J : ℝ)
    (center : ℕ → ℝ) (hm : 1 ≤ bulkSize k L) {l : ℕ} (hl : l ≤ k)
    (htop : |(∑ h, ∑ i, topCenters b center h i) - (J - 2 * tb)| ≤ 2)
    (htypes : ∀ i < k, |typeCenter b i center - nominalWeight k J (stepGap BD Bz k L) i| ≤ 2) :
    sourceCancellationBound (Conclusion.frequencyBound Bs BD Bz k L) b k tb center l ≤
      Real.exp (((k : ℝ) + 1) * sourceScaleConstant Bs BD Bz k * (bulkSize k L : ℝ)) := by
  apply Real.exp_le_exp.mpr
  have hnonneg : 0 ≤ sourceScaleConstant Bs BD Bz k * (bulkSize k L : ℝ) :=
    mul_nonneg (sourceScaleConstant_pos Bs BD Bz k).le (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ j ∈ Finset.range l, sourceScaleConstant Bs BD Bz k * (bulkSize k L : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact max_le hnonneg (sourceCancellationExponent_le_linear Bs BD Bz b k L tb J center hm
        ((Finset.mem_range.mp hj).trans_le hl) htop htypes)
    _ = (l : ℝ) * (sourceScaleConstant Bs BD Bz k * (bulkSize k L : ℝ)) := by simp
    _ ≤ ((k : ℝ) + 1) * (sourceScaleConstant Bs BD Bz k * (bulkSize k L : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ hnonneg
      have hh : (l : ℝ) ≤ k := by exact_mod_cast hl
      linarith
    _ = _ := by ring

theorem exists_sourceCancellationBound_le_exp_linear (Bs BD Bz : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ b : ℕ, ∀ L tb J : ℝ, ∀ center : ℕ → ℝ,
      1 ≤ bulkSize k L → ∀ l ≤ k,
      |(∑ h, ∑ i, topCenters b center h i) - (J - 2 * tb)| ≤ 2 →
      (∀ i < k, |typeCenter b i center - nominalWeight k J (stepGap BD Bz k L) i| ≤ 2) →
      sourceCancellationBound (Conclusion.frequencyBound Bs BD Bz k L) b k tb center l ≤
        Real.exp (C * (bulkSize k L : ℝ)) := by
  refine ⟨((k : ℝ) + 1) * sourceScaleConstant Bs BD Bz k,?_,?_⟩
  · exact mul_pos (by positivity) (sourceScaleConstant_pos Bs BD Bz k)
  · intro b L tb J center hm l hl htop htypes
    exact sourceCancellationBound_le_exp_linear Bs BD Bz b k L tb J center hm hl htop htypes

end Ostmann.Arithmetic.HistorySymbolicEncoding

end

end OAI
