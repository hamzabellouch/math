import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.ScaleInvariantExcessPropagation

namespace OAI

/-!
# Dyadic descendant radii

The radius at depth `j` is the original radius divided by `2 ^ j`. Rescaling by
another dyadic power either returns to a shallower descendant or passes to a
larger original scale. Positivity and the support-diameter bound ensure that an
admissible dyadic horizon remains admissible for every descendant.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def descendantRadius (r : ℝ) (j : ℕ) : ℝ := r / (2 : ℝ) ^ j

theorem descendantRadius_pos (r : ℝ) (hr : 0 < r) (j : ℕ) : 0 < descendantRadius r j := by
  unfold descendantRadius
  positivity

theorem descendantRadius_zero (r : ℝ) : descendantRadius r 0 = r := by
  simp [descendantRadius]

theorem descendantRadius_half (r : ℝ) (j : ℕ) :
    descendantRadius r j * (1 / 2 : ℝ) = descendantRadius r (j + 1) := by
  simp only [descendantRadius, pow_succ]
  ring

theorem descendantRadius_mul_dyadic_small (r : ℝ) (j l : ℕ) (hl : l ≤ j) :
    descendantRadius r j * (2 : ℝ) ^ l = descendantRadius r (j - l) := by
  have hp : (2 : ℝ) ^ j = (2 : ℝ) ^ (j - l) * (2 : ℝ) ^ l := by
    rw [← pow_add, Nat.sub_add_cancel hl]
  simp only [descendantRadius, hp]
  field_simp

theorem descendantRadius_mul_dyadic_large (r : ℝ) (j l : ℕ) (hl : j ≤ l) :
    descendantRadius r j * (2 : ℝ) ^ l = r * (2 : ℝ) ^ (l - j) := by
  have hp : (2 : ℝ) ^ l = (2 : ℝ) ^ j * (2 : ℝ) ^ (l - j) := by
    rw [← pow_add, Nat.add_sub_of_le hl]
  simp only [descendantRadius, hp]
  field_simp

theorem descendantRadius_admissible_horizon {d : ℕ} (μ : Measure (Ambient d))
    (r : ℝ) (hr : 0 < r) (j K : ℕ) (h : AdmissibleRadius μ (r * (2 : ℝ) ^ K)) :
    AdmissibleRadius μ (descendantRadius r j * (2 : ℝ) ^ K) := by
  have hpow : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hle : descendantRadius r j ≤ r := by
    exact (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ j)).mpr
      (le_mul_of_one_le_right hr.le hpow)
  refine ⟨mul_pos (descendantRadius_pos r hr j) (by positivity), ?_⟩
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hle (by positivity))).trans h.2

end

end RieszRectifiability

end OAI
