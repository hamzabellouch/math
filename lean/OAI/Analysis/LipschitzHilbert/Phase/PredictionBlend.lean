import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import OAI.Analysis.LipschitzHilbert.Phase.PredictionNormalization

namespace OAI

/-! Absorbing the residual denominator error by the actual convex blend. -/

noncomputable section

namespace LipschitzHilbert

theorem blended_prediction_pos {b θ : ℝ} (hb : 0 < b)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : 0 < (1 - θ) * b + θ := by
  by_cases hθ : θ = 1
  · simp [hθ]
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr (lt_of_le_of_ne hθ1 hθ)) hb) hθ0

/-- Concavity provides a gain measured by the negative logarithm of the
unblended prediction. -/
theorem blended_prediction_log_gain {b θ : ℝ} (hb : 0 < b)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    -θ * Real.log b ≤ Real.log ((1 - θ) * b + θ) - Real.log b := by
  have h := strictConcaveOn_log_Ioi.concaveOn.2 hb (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (sub_nonneg.mpr hθ1) hθ0 (by ring : (1 - θ) + θ = 1)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero, mul_one] at h
  linarith

/-- The coefficient of the residual denominator can be canceled by choosing
the blending weight at least as large as its error coefficient. -/
theorem blended_prediction_domination {β b θ a e r d u : ℝ}
    (hβ : 0 < β) (hb : 0 < b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hr : 0 ≤ r) (he : e ≤ θ)
    (hcomparison : Real.log β - Real.log b ≤ a * u + e * r)
    (hdeficit : r - d * u ≤ -Real.log b) :
    β ≤ Real.exp ((a + θ * d) * u) * ((1 - θ) * b + θ) := by
  have hgain := blended_prediction_log_gain hb hθ0 hθ1
  have hscaled := mul_le_mul_of_nonneg_left hdeficit hθ0
  have herr := mul_le_mul_of_nonneg_right he hr
  have hlog : Real.log β ≤ (a + θ * d) * u + Real.log ((1 - θ) * b + θ) := by
    nlinarith
  calc
    β = Real.exp (Real.log β) := (Real.exp_log hβ).symm
    _ ≤ Real.exp ((a + θ * d) * u + Real.log ((1 - θ) * b + θ)) :=
      Real.exp_le_exp.mpr hlog
    _ = _ := by rw [Real.exp_add, Real.exp_log (blended_prediction_pos hb hθ0 hθ1)]

/-- In the balanced case `u ≥ 1/2`, a bounded model logarithm has the same
relative-drop form after blending. -/
theorem balanced_blended_prediction_domination {β b θ a d u : ℝ}
    (hβ : 0 < β) (hb : 0 < b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hd : 0 ≤ d) (hu : 1 / 2 ≤ u)
    (hcomparison : Real.log β - Real.log b ≤ a * u)
    (hupper : Real.log b ≤ d) :
    β ≤ Real.exp ((a + 2 * θ * d) * u) * ((1 - θ) * b + θ) := by
  have hdeficit : (0 : ℝ) - (2 * d) * u ≤ -Real.log b := by
    nlinarith [mul_le_mul_of_nonneg_left hu hd]
  have h := blended_prediction_domination hβ hb hθ0 hθ1 (le_refl (0 : ℝ)) hθ0
    (show Real.log β - Real.log b ≤ a * u + 0 * 0 by simpa using hcomparison)
    hdeficit
  have heq : a + θ * (2 * d) = a + 2 * θ * d := by ring
  rw [heq] at h
  exact h

end LipschitzHilbert

end

end OAI
