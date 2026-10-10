import OAI.Analysis.LipschitzHilbert.Phase.PhaseMotion

namespace OAI

/-! Replacing a top's carrier by its angular child-center carrier costs
only the child width, not the width of an earlier block ancestor. -/

noncomputable section
namespace LipschitzHilbert
open PhaseCombinatorics

variable {κ : Type*} [Fintype κ]

theorem diagonalModulation_change_slope (frequency : κ → ℝ)
    (v : EuclideanSpace ℂ κ) (F : ℝ) (hF : 0 ≤ F)
    (hfrequency : ∀ k, |frequency k| ≤ F) (reference top center b : ℝ) :
    ‖diagonalModulation frequency v ((reference-top)*b)-
      diagonalModulation frequency v ((reference-center)*b)‖ ≤
      F*‖v‖*|top-center| * |b| := by
  have h := diagonalModulation_motion frequency v hF hfrequency
    ((reference-center)*b) ((reference-top)*b)
  have heq : (reference-top)*b-(reference-center)*b = (center-top)*b := by ring
  rw [heq, abs_mul, abs_sub_comm center top] at h
  simpa only [mul_assoc] using h

/-- A bound in the top carrier transfers to the one common child carrier. -/
theorem carrier_replacement_motion (frequency : κ → ℝ)
    (v0 v1 : EuclideanSpace ℂ κ) (F B E : ℝ) (hF : 0 ≤ F)
    (hfrequency : ∀ k, |frequency k| ≤ F) (hB : ‖v0‖ ≤ B)
    (reference top center b : ℝ)
    (hmotion : ‖v1-diagonalModulation frequency v0 ((reference-top)*b)‖ ≤ E) :
    ‖v1-diagonalModulation frequency v0 ((reference-center)*b)‖ ≤
      E+F*B*|top-center| * |b| := by
  apply (norm_sub_le_norm_sub_add_norm_sub v1
    (diagonalModulation frequency v0 ((reference-top)*b))
    (diagonalModulation frequency v0 ((reference-center)*b))).trans
  apply add_le_add hmotion
  apply (diagonalModulation_change_slope frequency v0 F hF hfrequency reference top center b).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hF) (abs_nonneg _)) (abs_nonneg _)

/-- At the source averaging scale the carrier replacement is of order
G^(-1/2), uniformly in the absolute frequency center. -/
theorem source_carrier_replacement_budget {F C w rho G d b : ℝ}
    (_hF : 0 ≤ F) (hC : 0 ≤ C) (hw : 0 < w) (hrho : 0 < rho) (hG : 0 < G)
    (hfrequency : F ≤ C/w) (hslope : |d| ≤ rho)
    (hdisplacement : |b| ≤ w/(rho*Real.sqrt G)) :
    F*|d| * |b| ≤ C/Real.sqrt G := by
  calc
    _ ≤ (C/w)*rho*(w/(rho*Real.sqrt G)) :=
      mul_le_mul (mul_le_mul hfrequency hslope (abs_nonneg _) (div_nonneg hC hw.le))
        hdisplacement (abs_nonneg _) (mul_nonneg (div_nonneg hC hw.le) hrho.le)
    _ = _ := by field_simp [hw.ne', hrho.ne', (Real.sqrt_pos.mpr hG).ne']

end LipschitzHilbert

end

end OAI
