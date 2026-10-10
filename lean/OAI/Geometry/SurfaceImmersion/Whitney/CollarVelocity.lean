import Mathlib

namespace OAI

/-! An explicit small circular arc and positive averaging density. This gives
an alternative collar construction without solving a squared-amplitude equation. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

/-- Rational parametrization of a small arc around `(1,0)`. -/
def arcX (a t : ℝ) : ℝ := (1 - (a * Real.cos t) ^ 2) / (1 + (a * Real.cos t) ^ 2)
def arcY (a t : ℝ) : ℝ := (2 * (a * Real.cos t)) / (1 + (a * Real.cos t) ^ 2)

/-- A positive density that makes the two mean constraints elementary. -/
def density (a t : ℝ) : ℝ := (1 + (a * Real.cos t) ^ 2) / (1 + a ^ 2 / 2)

lemma arcDen_pos (a t : ℝ) : 0 < 1 + (a * Real.cos t) ^ 2 := by positivity
lemma densityDen_pos (a : ℝ) : 0 < 1 + a ^ 2 / 2 := by positivity

lemma arc_unit (a t : ℝ) : arcX a t ^ 2 + arcY a t ^ 2 = 1 := by
  unfold arcX arcY
  field_simp [(arcDen_pos a t).ne']
  ring

lemma density_pos (a t : ℝ) : 0 < density a t :=
  div_pos (arcDen_pos a t) (densityDen_pos a)

lemma density_mul_arcX (a t : ℝ) :
    density a t * arcX a t = (1 - (a * Real.cos t) ^ 2) / (1 + a ^ 2 / 2) := by
  unfold density arcX
  field_simp [(arcDen_pos a t).ne', (densityDen_pos a).ne']

lemma density_mul_arcY (a t : ℝ) :
    density a t * arcY a t = 2 * a * Real.cos t / (1 + a ^ 2 / 2) := by
  unfold density arcY
  field_simp [(arcDen_pos a t).ne', (densityDen_pos a).ne']

@[simp] lemma arcX_zero (t : ℝ) : arcX 0 t = 1 := by simp [arcX]
@[simp] lemma arcY_zero (t : ℝ) : arcY 0 t = 0 := by simp [arcY]
@[simp] lemma density_zero (t : ℝ) : density 0 t = 1 := by simp [density]

lemma arcX_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => arcX z.1 z.2) := by
  exact (contDiff_const.sub ((contDiff_fst.mul contDiff_snd.cos).pow 2)).div
    (contDiff_const.add ((contDiff_fst.mul contDiff_snd.cos).pow 2))
    (fun z => (arcDen_pos z.1 z.2).ne')

lemma arcY_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => arcY z.1 z.2) := by
  exact (contDiff_const.mul (contDiff_fst.mul contDiff_snd.cos)).div
    (contDiff_const.add ((contDiff_fst.mul contDiff_snd.cos).pow 2))
    (fun z => (arcDen_pos z.1 z.2).ne')

lemma density_smooth : ContDiff ℝ ∞ (fun z : ℝ × ℝ => density z.1 z.2) := by
  exact (contDiff_const.add ((contDiff_fst.mul contDiff_snd.cos).pow 2)).div
    (contDiff_const.add (contDiff_fst.pow 2 |>.div_const 2))
    (fun z => (densityDen_pos z.1).ne')

lemma arcX_periodic (a : ℝ) : Function.Periodic (arcX a) (2 * Real.pi) := by
  intro t
  simp only [arcX, Real.cos_add_two_pi]

lemma arcY_periodic (a : ℝ) : Function.Periodic (arcY a) (2 * Real.pi) := by
  intro t
  simp only [arcY, Real.cos_add_two_pi]

lemma density_periodic (a : ℝ) : Function.Periodic (density a) (2 * Real.pi) := by
  intro t
  simp only [density, Real.cos_add_two_pi]

end ClosedSurfaceR4.CollarVelocity

end

end OAI
