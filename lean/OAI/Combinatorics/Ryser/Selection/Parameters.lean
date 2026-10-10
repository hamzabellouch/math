import OAI.Combinatorics.Ryser.Selection.DensityConstants
import OAI.Combinatorics.Ryser.Selection.KChoice

namespace OAI

noncomputable section
namespace RyserCoveringCounterexample.Selection

def selectionCutoff (D : ℕ) : ℝ := 1 / (4 * equationBound D)
def selectionSmallFactor (D : ℕ) : ℝ := 6 * equationBound D * Real.exp 1 * (D : ℝ)
def selectionLargeFactor (D : ℕ) : ℝ := (Real.exp 1 * (D : ℝ) / selectionCutoff D) * 3
def selectionSmallCoefficient (D K : ℕ) : ℝ := selectionSmallFactor D * (K : ℝ) ^ 2
def selectionLargeCoefficient (D K : ℕ) : ℝ := selectionLargeFactor D * (K : ℝ) ^ 2

theorem equationBound_pos (D : ℕ) (hD : 1 ≤ D) : 0 < equationBound D := by
  have hDr : (0 : ℝ) < D := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hD)
  unfold equationBound
  positivity

theorem selectionCutoff_pos (D : ℕ) (hD : 1 ≤ D) : 0 < selectionCutoff D := by
  unfold selectionCutoff
  exact div_pos zero_lt_one (mul_pos (by norm_num) (equationBound_pos D hD))

theorem selectionSmallFactor_pos (D : ℕ) (hD : 1 ≤ D) :
    0 < selectionSmallFactor D := by
  have hC := equationBound_pos D hD
  have hDr : (0 : ℝ) < D := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hD)
  unfold selectionSmallFactor
  positivity

theorem selectionLargeFactor_pos (D : ℕ) (hD : 1 ≤ D) :
    0 < selectionLargeFactor D := by
  have hc := selectionCutoff_pos D hD
  have hDr : (0 : ℝ) < D := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hD)
  unfold selectionLargeFactor
  positivity

theorem selectionSmallCoefficient_nonneg (D K : ℕ) (hD : 1 ≤ D) :
    0 ≤ selectionSmallCoefficient D K :=
  mul_nonneg (selectionSmallFactor_pos D hD).le (sq_nonneg _)

theorem selectionLargeCoefficient_nonneg (D K : ℕ) (hD : 1 ≤ D) :
    0 ≤ selectionLargeCoefficient D K :=
  mul_nonneg (selectionLargeFactor_pos D hD).le (sq_nonneg _)

theorem exists_selection_pool_size (D : ℕ) :
    ∃ K : ℕ, 6 ≤ K ∧
      selectionSmallCoefficient D K * (1 / 2 : ℝ) ^ (K - 3) ≤ 1 / 2 ∧
      selectionLargeCoefficient D K * Real.exp (2 - (K : ℝ) * densityDelta D) < 1 / 2 :=
  exists_pool_size (selectionSmallFactor D) (selectionLargeFactor D) (densityDelta_pos D)

end RyserCoveringCounterexample.Selection

end

end OAI
