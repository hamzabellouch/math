import OAI.Geometry.SurfaceImmersion.Whitney.CollarVelocityTurns

namespace OAI

/-! Interpolate the collar angle to a circle-covering interior angle without extra turns. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

def blendedAngle (a A s h t : ℝ) : ℝ :=
  h + (1 - s) * baseAngle a t + s * (A * Real.cos t)

lemma hasDerivAt_blendedAngle (a A s h t : ℝ) :
    HasDerivAt (blendedAngle a A s h)
      (-Real.sin t * ((1 - s) * (2 * a / (1 + (a * Real.cos t) ^ 2)) + s * A)) t := by
  have hd := (((hasDerivAt_baseAngle a t).const_mul (1 - s)).add
    (((Real.hasDerivAt_cos t).const_mul A).const_mul s)).const_add h
  convert hd using 1
  · funext u
    simp only [blendedAngle, Pi.add_apply]
    ring
  · ring

lemma blended_speed_positive {a A s : ℝ} (ha : 0 < a) (hA : 0 < A)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (t : ℝ) :
    0 < (1 - s) * (2 * a / (1 + (a * Real.cos t) ^ 2)) + s * A := by
  have hd : 0 < 2 * a / (1 + (a * Real.cos t) ^ 2) :=
    div_pos (by positivity) (arcDen_pos a t)
  by_cases hz : s = 0
  · simpa only [hz, sub_zero, one_mul, zero_mul, add_zero] using hd
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr hs1) hd.le) (mul_pos (lt_of_le_of_ne hs (Ne.symm hz)) hA)

/-- All interpolation parameters preserve the same two stationary positions. -/
lemma blended_deriv_eq_zero_iff {a A s : ℝ} (ha : 0 < a) (hA : 0 < A)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (h t : ℝ) :
    deriv (blendedAngle a A s h) t = 0 ↔ Real.sin t = 0 := by
  rw [(hasDerivAt_blendedAngle a A s h t).deriv]
  simp [(blended_speed_positive ha hA hs hs1 t).ne']

lemma blendedAngle_zero (a A s h : ℝ) :
    blendedAngle a A s h 0 = h + ((1 - s) * (2 * Real.arctan a) + s * A) := by
  simp [blendedAngle, baseAngle]
  ring

lemma blendedAngle_pi (a A s h : ℝ) :
    blendedAngle a A s h Real.pi = h - ((1 - s) * (2 * Real.arctan a) + s * A) := by
  simp [blendedAngle, baseAngle, Real.arctan_neg]
  ring

/-- The interior angle covers every direction once its amplitude exceeds pi. -/
lemma interior_angle_covers {A β : ℝ} (hA : Real.pi ≤ A)
    (hβ : β ∈ Set.Icc (-Real.pi) Real.pi) :
    ∃ t ∈ Set.Icc (0 : ℝ) Real.pi, A * Real.cos t = β := by
  have hAp : 0 < A := lt_of_lt_of_le Real.pi_pos hA
  have hl : -1 ≤ β / A := (le_div_iff₀ hAp).2 (by linarith [hβ.1])
  have hu : β / A ≤ 1 := (div_le_iff₀ hAp).2 (by linarith [hβ.2])
  refine ⟨Real.arccos (β / A), ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩, ?_⟩
  rw [Real.cos_arccos hl hu]
  field_simp

end ClosedSurfaceR4.CollarVelocity

end

end OAI
