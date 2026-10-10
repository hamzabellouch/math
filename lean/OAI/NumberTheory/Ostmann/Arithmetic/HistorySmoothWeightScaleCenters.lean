import OAI.NumberTheory.Ostmann.Arithmetic.HistoryProductWindowsNormalize
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightRelativeConstants

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open HistoryProductWindows Construction InitialCoordinatesTemplate

theorem sourceCancellationExponent_le_nominal (V : ℕ → ℕ) (b k : ℕ)
    (tb J : ℝ) (Δ center : ℕ → ℝ) {j : ℕ} (hj : j < k)
    (htop : |(∑ h, ∑ i, topCenters b center h i) - (J - 2 * tb)| ≤ 2)
    (htypes : ∀ i < k, |typeCenter b i center - nominalWeight k J Δ i| ≤ 2) :
    sourceCancellationExponent V b k tb center j ≤
      Real.log ((V j : ℝ) + 1) + Δ j + nominalInheritedWidth k j + nominalRemovedWidth k j + 1 := by
  have hI := (abs_le.mp (inheritedCenter_nominal_error b k j tb J
    (nominalWeight k J Δ) center htop htypes)).2
  have hR := (abs_le.mp (removedCenter_nominal_error b k j hj
    (nominalWeight k J Δ) center htypes)).1
  have hp : 0 ≤ (2 : ℝ)^j := by positivity
  have hI' := mul_le_mul_of_nonneg_left hI hp
  have hR' := mul_le_mul_of_nonneg_left hR hp
  have hrec := nominalWeight_recurrence_scaled hj J Δ
  unfold sourceCancellationExponent nominalInheritedWidth nominalRemovedWidth inheritedWidth removedWidth
  nlinarith

theorem nominal_widths_le (k : ℕ) {j : ℕ} (hj : j ≤ k) :
    nominalInheritedWidth k j + nominalRemovedWidth k j + 1 ≤
      2 + (2 : ℝ)^k * (18 + 10 * (k : ℝ)) := by
  have hp := mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj)
    (show 0 ≤ 18 + 10 * (k : ℝ) by positivity)
  unfold nominalInheritedWidth nominalRemovedWidth
  nlinarith

end Ostmann.Arithmetic.HistorySymbolicEncoding

end

end OAI
