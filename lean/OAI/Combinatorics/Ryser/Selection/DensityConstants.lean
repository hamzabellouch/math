import OAI.Combinatorics.Ryser.Selection.ChunkTail
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Selection

def densityChunkCount (D : ℕ) : ℕ := 16 * D ^ 4 + 1

def densityAlpha (D : ℕ) : ℝ := 1 / (4 * (D : ℝ) ^ 3)

def densityDelta (D : ℕ) : ℝ := (1 / 2 : ℝ) ^ (densityChunkCount D + 1)

def densityGamma (D : ℕ) : ℝ :=
  densityDelta D / (2 * (densityAlpha D + 4 * (D : ℝ) ^ 3))

def densityRate (D : ℕ) : ℝ := densityGamma D / 4

theorem densityAlpha_pos (D : ℕ) (hD : 1 ≤ D) : 0 < densityAlpha D := by
  have hDr : (0 : ℝ) < D := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  unfold densityAlpha
  positivity

theorem densityDelta_pos (D : ℕ) : 0 < densityDelta D := by
  unfold densityDelta
  exact pow_pos (by norm_num) _

theorem densityGamma_pos (D : ℕ) (hD : 1 ≤ D) : 0 < densityGamma D := by
  have hα := densityAlpha_pos D hD
  have hδ := densityDelta_pos D
  unfold densityGamma
  positivity

theorem densityRate_pos (D : ℕ) (hD : 1 ≤ D) : 0 < densityRate D := by
  unfold densityRate
  exact div_pos (densityGamma_pos D hD) (by norm_num)

theorem equationBound_mul_densityAlpha (D : ℕ) (hD : 1 ≤ D) :
    equationBound D * densityAlpha D = 1 / 2 := by
  have hDr : (0 : ℝ) < D := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  unfold equationBound densityAlpha
  field_simp [hDr.ne']; ring

theorem density_error_budget (D : ℕ) (hD : 1 ≤ D) :
    2 * ((densityAlpha D + 2 * equationBound D) * densityGamma D) =
      densityDelta D := by
  have hα := densityAlpha_pos D hD
  have hden : densityAlpha D + 4 * (D : ℝ) ^ 3 ≠ 0 := by
    have hpos : 0 < densityAlpha D + 4 * (D : ℝ) ^ 3 := by positivity
    exact hpos.ne'
  unfold densityGamma equationBound
  field_simp [hden]; ring

theorem density_chunkCount_identity (D : ℕ) :
    (densityChunkCount D : ℝ) = 4 * (D : ℝ) / densityAlpha D + 1 := by
  simp only [densityChunkCount, densityAlpha, Nat.cast_add, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat, one_div, div_inv_eq_mul]
  ring

theorem regularTailConstant_pos (D : ℕ) (hD : 1 ≤ D) (γ : ℝ) (hγ : 0 < γ) :
    0 < regularTailConstant D γ := by
  have hDr : (0 : ℝ) < D := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD)
  unfold regularTailConstant equationBound
  positivity

end RyserCoveringCounterexample.Selection

end

end OAI
