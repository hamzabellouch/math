import OAI.Geometry.SurfaceImmersion.Whitney.CollarVelocityReparam

namespace OAI

/-! The explicit collar arc has exactly two stationary angular positions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

def baseAngle (a t : ℝ) : ℝ := 2 * Real.arctan (a * Real.cos t)
def angle (a θ : ℝ) : ℝ := baseAngle a (inverseClock a θ)

lemma baseAngle_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => baseAngle z.1 z.2) :=
  contDiff_const.mul ((contDiff_fst.mul contDiff_snd.cos).arctan)

lemma angle_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => angle z.1 z.2) :=
  baseAngle_smooth.comp (contDiff_fst.prodMk inverseClock_smooth)

lemma cos_baseAngle (a t : ℝ) : Real.cos (baseAngle a t) = arcX a t := by
  rw [baseAngle, Real.cos_two_mul, Real.cos_sq_arctan]
  unfold arcX
  field_simp [(arcDen_pos a t).ne']
  ring

lemma sin_baseAngle (a t : ℝ) : Real.sin (baseAngle a t) = arcY a t := by
  rw [baseAngle, Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  unfold arcY
  have hs : Real.sqrt (1 + (a * Real.cos t) ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 (arcDen_pos a t)).ne'
  field_simp [hs]
  rw [Real.sq_sqrt (by positivity)]

lemma cos_angle (a θ : ℝ) : Real.cos (angle a θ) = reparamX a θ :=
  cos_baseAngle a (inverseClock a θ)

lemma sin_angle (a θ : ℝ) : Real.sin (angle a θ) = reparamY a θ :=
  sin_baseAngle a (inverseClock a θ)

lemma hasDerivAt_baseAngle (a t : ℝ) :
    HasDerivAt (baseAngle a) (-2 * a * Real.sin t / (1 + (a * Real.cos t) ^ 2)) t := by
  convert (((Real.hasDerivAt_cos t).const_mul a).arctan.const_mul 2) using 1
  · rfl
  · field_simp [(arcDen_pos a t).ne']

lemma hasDerivAt_inverseClock (a θ : ℝ) :
    HasDerivAt (inverseClock a) (density a (inverseClock a θ))⁻¹ θ := by
  have hi : Differentiable ℝ (inverseClock a) :=
    (inverseClock_smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hc := (hasDerivAt_clock a (inverseClock a θ)).comp θ (hi θ).hasDerivAt
  have hid : (fun x => clock a (inverseClock a x)) = id := by funext x; simp
  change HasDerivAt (fun x => clock a (inverseClock a x)) _ θ at hc
  rw [hid] at hc
  have heq : density a (inverseClock a θ) * deriv (inverseClock a) θ = 1 :=
    hc.unique (hasDerivAt_id θ)
  convert (hi θ).hasDerivAt using 1
  apply mul_left_cancel₀ (density_pos a (inverseClock a θ)).ne'
  rw [mul_inv_cancel₀ (density_pos a (inverseClock a θ)).ne', heq]

lemma deriv_angle (a θ : ℝ) :
    deriv (angle a) θ =
      (-2 * a * Real.sin (inverseClock a θ) /
        (1 + (a * Real.cos (inverseClock a θ)) ^ 2)) *
          (density a (inverseClock a θ))⁻¹ :=
  ((hasDerivAt_baseAngle a (inverseClock a θ)).comp θ
    (hasDerivAt_inverseClock a θ)).deriv

lemma deriv_angle_eq_zero_iff {a θ : ℝ} (ha : a ≠ 0) :
    deriv (angle a) θ = 0 ↔ Real.sin (inverseClock a θ) = 0 := by
  rw [deriv_angle]
  simp [(density_pos a (inverseClock a θ)).ne', (arcDen_pos a (inverseClock a θ)).ne', ha]

end ClosedSurfaceR4.CollarVelocity

end

end OAI
