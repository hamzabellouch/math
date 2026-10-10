import OAI.Geometry.RCD.Heat.DiscreteGaussianComparison
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace OAI

/-! # The hyperbolic comparison chord and its exact neighboring-point identity -/

noncomputable section
namespace RegularPointCoordinates

def hyperbolicChord (c A B t : ℝ) : ℝ :=
  (Real.sinh (c*(1-t))*A+Real.sinh (c*t)*B)/Real.sinh c

@[simp] theorem hyperbolicChord_zero {c : ℝ} (hc : 0 < c) (A B : ℝ) :
    hyperbolicChord c A B 0=A := by
  simp [hyperbolicChord,(Real.sinh_pos_iff.mpr hc).ne']

@[simp] theorem hyperbolicChord_one {c : ℝ} (hc : 0 < c) (A B : ℝ) :
    hyperbolicChord c A B 1=B := by
  simp [hyperbolicChord,(Real.sinh_pos_iff.mpr hc).ne']

theorem continuous_hyperbolicChord (c A B : ℝ) : Continuous (hyperbolicChord c A B) := by
  unfold hyperbolicChord
  fun_prop

theorem hyperbolicChord_nonneg {c A B t : ℝ} (hc : 0 < c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ hyperbolicChord c A B t := by
  apply div_nonneg _ (Real.sinh_pos_iff.mpr hc).le
  exact add_nonneg (mul_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg hc.le (sub_nonneg.mpr ht1))) hA)
    (mul_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg hc.le ht0)) hB)

theorem hyperbolicChord_neighbor_sum (c A B t h : ℝ) :
    hyperbolicChord c A B (t-h)+hyperbolicChord c A B (t+h)=
      2*Real.cosh (c*h)*hyperbolicChord c A B t := by
  have h₀ : c*(1-(t-h))=c*(1-t)+c*h := by ring
  have h₁ : c*(1-(t+h))=c*(1-t)-c*h := by ring
  have h₂ : c*(t-h)=c*t-c*h := by ring
  have h₃ : c*(t+h)=c*t+c*h := by ring
  unfold hyperbolicChord
  rw [h₀,h₁,h₂,h₃,Real.sinh_add,Real.sinh_sub,Real.sinh_sub,Real.sinh_add]
  ring

end RegularPointCoordinates

end

end OAI
