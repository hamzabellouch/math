import OAI.Geometry.SurfaceImmersion.Whitney.CollarVelocity

namespace OAI

/-! The explicit positive change of angular variable for the collar arc. -/
noncomputable section
open Filter
open scoped Topology ContDiff

namespace ClosedSurfaceR4.CollarVelocity

def clock (a t : ℝ) : ℝ := t + a ^ 2 / (2 * (2 + a ^ 2)) * Real.sin (2 * t)

lemma density_eq (a t : ℝ) :
    density a t = 1 + a ^ 2 / (2 + a ^ 2) * Real.cos (2 * t) := by
  rw [Real.cos_two_mul]
  unfold density
  have h : 2 + a ^ 2 ≠ 0 := by positivity
  field_simp [(densityDen_pos a).ne', h]
  ring

lemma hasDerivAt_clock (a t : ℝ) : HasDerivAt (clock a) (density a t) t := by
  have hs := (Real.hasDerivAt_sin (2 * t)).comp t ((hasDerivAt_id t).const_mul 2)
  have h := (hasDerivAt_id t).add (hs.const_mul (a ^ 2 / (2 * (2 + a ^ 2))))
  change HasDerivAt (fun t => t + a ^ 2 / (2 * (2 + a ^ 2)) * Real.sin (2 * t)) _ t
  convert h using 1
  · rfl
  · rw [density_eq]
    have hd : 2 + a ^ 2 ≠ 0 := by positivity
    field_simp [hd]

lemma clock_strictMono (a : ℝ) : StrictMono (clock a) := by
  apply strictMono_of_deriv_pos
  intro t
  rw [(hasDerivAt_clock a t).deriv]
  exact density_pos a t

lemma clock_continuous (a : ℝ) : Continuous (clock a) :=
  (show Differentiable ℝ (clock a) from fun t => (hasDerivAt_clock a t).differentiableAt).continuous

lemma clock_period (a t : ℝ) : clock a (t + 2 * Real.pi) = clock a t + 2 * Real.pi := by
  unfold clock
  rw [show 2 * (t + 2 * Real.pi) = (2 * t + 2 * Real.pi) + 2 * Real.pi by ring]
  rw [Real.sin_add_two_pi, Real.sin_add_two_pi]
  ring

lemma clock_displacement_bound (a t : ℝ) :
    |clock a t - t| ≤ |a ^ 2 / (2 * (2 + a ^ 2))| := by
  unfold clock
  rw [add_sub_cancel_left, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

lemma clock_surjective (a : ℝ) : Function.Surjective (clock a) := by
  let C := |a ^ 2 / (2 * (2 + a ^ 2))|
  have hlo (t : ℝ) : t - C ≤ clock a t := by
    have h := (abs_le.mp (clock_displacement_bound a t)).1
    dsimp [C]
    linarith
  have hhi (t : ℝ) : clock a t ≤ t + C := by
    have h := (abs_le.mp (clock_displacement_bound a t)).2
    dsimp [C]
    linarith
  apply (clock_continuous a).surjective
  · apply tendsto_atTop_mono hlo
    simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-C) tendsto_id
  · exact tendsto_atBot_mono hhi (tendsto_atBot_add_const_right atBot C tendsto_id)

end ClosedSurfaceR4.CollarVelocity

end

end OAI
