import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternPublishedInputs

namespace OAI

/-! Exact centre, radius, and critical-edge arithmetic for the displayed MP density. -/
noncomputable section
namespace InvariantIsing

lemma mp_edge_centre_radius {α : ℝ} (hα : 0 ≤ α) :
    marchenkoPasturA α = 1+α-2*Real.sqrt α ∧
    marchenkoPasturB α = 1+α+2*Real.sqrt α := by
  have hs := Real.sq_sqrt hα
  constructor
  · unfold marchenkoPasturA
    nlinarith
  · unfold marchenkoPasturB
    nlinarith

lemma mp_radius_positive {α : ℝ} (hα : 0 < α) : 0 < 2*Real.sqrt α := by positivity

lemma mp_centre_exceeds_radius {α : ℝ} (hα : 0 ≤ α) (hne : α ≠ 1) :
    |2*Real.sqrt α| < 1+α := by
  have hs := Real.sq_sqrt hα
  have hne' : Real.sqrt α ≠ 1 := by intro h; rw [h] at hs; norm_num at hs; exact hne hs.symm
  have hp := sq_pos_of_ne_zero (sub_ne_zero.mpr hne')
  rw [abs_of_nonneg (by positivity)]
  nlinarith

lemma mp_centre_radius_discriminant {α : ℝ} (hα : 0 ≤ α) :
    (1+α)^2-(2*Real.sqrt α)^2 = (α-1)^2 := by
  have hs := Real.sq_sqrt hα
  nlinarith

lemma mp_centre_radius_sqrt {α : ℝ} (hα : 0 ≤ α) :
    Real.sqrt ((1+α)^2-(2*Real.sqrt α)^2) = |α-1| := by
  rw [mp_centre_radius_discriminant hα,Real.sqrt_sq_eq_abs]

lemma mp_continuous_mass (α : ℝ) : (1+α-|α-1|)/2 = min 1 α := by
  rcases le_total α 1 with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h),min_eq_right h]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr h),min_eq_left h]
    ring

lemma mp_total_mass (α : ℝ) : max (1-α) 0+min 1 α = 1 := by
  rcases le_total α 1 with h | h
  · rw [max_eq_left (sub_nonneg.mpr h),min_eq_right h]
    ring
  · rw [max_eq_right (sub_nonpos.mpr h),min_eq_left h]
    simp

end InvariantIsing

end

end OAI
