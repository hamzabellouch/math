import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # A fixed exhaustion of space and strictly positive heat times -/

noncomputable section
namespace RegularPointCoordinates

def heatCompactRadius (m : ℕ) : ℝ := (m:ℝ)+1
def heatCompactTimeMargin (m : ℕ) : ℝ := 1/((m:ℝ)+2)

theorem heatCompactRadius_nonneg (m : ℕ) : 0 ≤ heatCompactRadius m := by
  unfold heatCompactRadius
  positivity

theorem heatCompactTimeMargin_pos (m : ℕ) : 0 < heatCompactTimeMargin m := by
  unfold heatCompactTimeMargin
  positivity

theorem heatCompactTimeMargin_le_one (m : ℕ) : heatCompactTimeMargin m ≤ 1 := by
  unfold heatCompactTimeMargin
  apply (div_le_iff₀ (by positivity : 0 < (m:ℝ)+2)).mpr
  have := Nat.cast_nonneg (α := ℝ) m
  linarith

theorem heat_exhaustion_contains (R : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ m, R ≤ heatCompactRadius m ∧ heatCompactTimeMargin m < δ := by
  obtain ⟨m,hm⟩ := exists_nat_gt (max R δ⁻¹)
  refine ⟨m,?_,?_⟩
  · have h := (le_max_left R δ⁻¹).trans_lt hm
    unfold heatCompactRadius
    linarith
  · have h := mul_lt_mul_of_pos_left ((le_max_right R δ⁻¹).trans_lt hm) hδ
    rw [mul_inv_cancel₀ hδ.ne'] at h
    unfold heatCompactTimeMargin
    apply (div_lt_iff₀ (by positivity : 0 < (m:ℝ)+2)).mpr
    nlinarith

end RegularPointCoordinates

end

end OAI
