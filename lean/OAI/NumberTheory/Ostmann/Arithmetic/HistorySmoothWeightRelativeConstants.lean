import OAI.NumberTheory.Ostmann.Arithmetic.HistoryProductWindows
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightPivotRatio

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open HistoryProductWindows

def sourceCancellationExponent (V : ℕ → ℕ) (b k : ℕ) (tb : ℝ)
    (center : ℕ → ℝ) (j : ℕ) : ℝ :=
  Real.log ((V j : ℝ) + 1) + (2 : ℝ) ^ j *
    (2 * tb + inheritedCenter b k j center - removedCenter b k j center) +
      inheritedWidth k j + removedWidth k j + 1

def sourceCancellationBound (V : ℕ → ℕ) (b k : ℕ) (tb : ℝ)
    (center : ℕ → ℝ) (l : ℕ) : ℝ :=
  Real.exp (∑ j ∈ Finset.range l, max 0 (sourceCancellationExponent V b k tb center j))

theorem sourceCancellationBound_one_le (V : ℕ → ℕ) (b k : ℕ) (tb : ℝ)
    (center : ℕ → ℝ) (l : ℕ) : 1 ≤ sourceCancellationBound V b k tb center l := by
  unfold sourceCancellationBound
  exact Real.one_le_exp (Finset.sum_nonneg fun j hj => le_max_left _ _)

theorem sourceCancellationExponent_exp_le (V : ℕ → ℕ) (b k : ℕ) (tb : ℝ)
    (center : ℕ → ℝ) {j l : ℕ} (hj : j < l) :
    Real.exp (sourceCancellationExponent V b k tb center j) ≤
      sourceCancellationBound V b k tb center l := by
  apply Real.exp_le_exp.mpr
  exact (le_max_right _ _).trans (Finset.single_le_sum
    (fun i hi => le_max_left _ _) (Finset.mem_range.mpr hj))

end Ostmann.Arithmetic.HistorySymbolicEncoding

end

end OAI
