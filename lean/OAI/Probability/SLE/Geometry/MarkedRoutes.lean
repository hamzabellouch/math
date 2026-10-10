import OAI.Probability.SLE.Geometry.WaypointRoutes
import OAI.Probability.SLE.Geometry.MarkedAccessHook

namespace OAI

/-! Two explicit finite routes from the marked point to the exterior
real boundary. One goes below the marked hook and exits on the left;
the other passes between its legs, above its top, and exits on the right. -/

noncomputable section
open Set Metric
open scoped Topology NNReal

namespace SLEExactGauge.Serpentine
open RibbonCoordinates

private def clippedVector (v : ℂ) (c t : ℝ) : ℂ :=
  (unitClip (t - c) : ℂ) * v

private lemma clippedVector_lipschitz {v : ℂ} (hv : ‖v‖ ≤ 6) (c : ℝ) :
    LipschitzWith 6 (clippedVector v c) := by
  apply LipschitzWith.of_dist_le_mul
  intro t u
  have hc := unitClip_lipschitz.dist_le_mul (t - c) (u - c)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, sub_sub_sub_cancel_right] at hc
  rw [clippedVector, clippedVector, dist_eq_norm, ← sub_mul, ← Complex.ofReal_sub,
    norm_mul, Complex.norm_real, Real.norm_eq_abs]
  norm_num only [NNReal.coe_ofNat]
  calc
    |unitClip (t - c) - unitClip (u - c)| * ‖v‖ ≤ |t - u| * 6 :=
      mul_le_mul hc hv (norm_nonneg _) (abs_nonneg _)
    _ = 6 * dist t u := by rw [Real.dist_eq]; ring

private lemma clippedVector_shift_lipschitz (w : ℂ) {v : ℂ} (hv : ‖v‖ ≤ 6) (c : ℝ) :
    LipschitzWith 6 (fun t => w + clippedVector v c t) := by
  apply LipschitzWith.of_dist_le_mul
  intro t u
  simpa only [dist_add_left] using (clippedVector_lipschitz hv c).dist_le_mul t u

def markedLeftRoute (w : ℂ) (a : ℝ) (t : ℝ) : ℂ :=
  w + clippedVector (-(a : ℂ) * Complex.I) 0 t +
    clippedVector ((-3 - w.re : ℝ) : ℂ) 1 t +
    clippedVector ((-1 - w.im + a : ℝ) * Complex.I) 2 t

def markedRightRoute (w : ℂ) (a : ℝ) (t : ℝ) : ℂ :=
  w + clippedVector ((-a / 2 : ℝ) + (a / 2 : ℝ) * Complex.I) 0 t +
    clippedVector ((2 + a / 2 - w.im : ℝ) * Complex.I) 1 t +
    clippedVector ((3 - w.re + a / 2 : ℝ) : ℂ) 2 t +
    clippedVector ((-3 - a : ℝ) * Complex.I) 3 t

@[simp] lemma markedLeftRoute_re (w : ℂ) (a t : ℝ) :
    (markedLeftRoute w a t).re = w.re + (-3 - w.re) * unitClip (t - 1) := by
  simp [markedLeftRoute, clippedVector]
  ring

@[simp] lemma markedLeftRoute_im (w : ℂ) (a t : ℝ) :
    (markedLeftRoute w a t).im = w.im - a * unitClip t +
      (-1 - w.im + a) * unitClip (t - 2) := by
  simp [markedLeftRoute, clippedVector]
  ring

@[simp] lemma markedRightRoute_re (w : ℂ) (a t : ℝ) :
    (markedRightRoute w a t).re = w.re - a / 2 * unitClip t +
      (3 - w.re + a / 2) * unitClip (t - 2) := by
  simp [markedRightRoute, clippedVector]
  ring

@[simp] lemma markedRightRoute_im (w : ℂ) (a t : ℝ) :
    (markedRightRoute w a t).im = w.im + a / 2 * unitClip t +
      (2 + a / 2 - w.im) * unitClip (t - 1) + (-3 - a) * unitClip (t - 3) := by
  simp [markedRightRoute, clippedVector]
  ring

lemma markedLeftRoute_zero (w : ℂ) (a : ℝ) : markedLeftRoute w a 0 = w := by
  apply Complex.ext <;> norm_num [unitClip]

lemma markedRightRoute_zero (w : ℂ) (a : ℝ) : markedRightRoute w a 0 = w := by
  apply Complex.ext <;> norm_num [unitClip]

lemma markedLeftRoute_final (w : ℂ) (a : ℝ) :
    markedLeftRoute w a 3 = (-3 : ℂ) - Complex.I := by
  apply Complex.ext <;> norm_num [unitClip]

lemma markedLeftRoute_four (w : ℂ) (a : ℝ) :
    markedLeftRoute w a 4 = (-3 : ℂ) - Complex.I := by
  apply Complex.ext <;> norm_num [unitClip]

lemma markedRightRoute_final (w : ℂ) (a : ℝ) :
    markedRightRoute w a 4 = (3 : ℂ) - Complex.I := by
  apply Complex.ext <;> norm_num [unitClip]; ring

lemma markedLeftRoute_continuous (w : ℂ) (a : ℝ) : Continuous (markedLeftRoute w a) := by
  have hc := unitClip_lipschitz.continuous
  unfold markedLeftRoute clippedVector
  fun_prop

lemma markedRightRoute_continuous (w : ℂ) (a : ℝ) : Continuous (markedRightRoute w a) := by
  have hc := unitClip_lipschitz.continuous
  unfold markedRightRoute clippedVector
  fun_prop

lemma markedLeftRoute_lipschitz {w : ℂ} (hw : ‖w‖ ≤ 1) {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) : LipschitzWith 24 (markedLeftRoute w a) := by
  have hr := (Complex.abs_re_le_norm w).trans hw
  have hi := (Complex.abs_im_le_norm w).trans hw
  have h0 : ‖-(a : ℂ) * Complex.I‖ ≤ 6 := by simpa [norm_mul, abs_of_nonneg ha] using (show a ≤ 6 by linarith)
  have h1 : ‖((-3 - w.re : ℝ) : ℂ)‖ ≤ 6 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      (show |-3 - w.re| ≤ 6 from abs_le.mpr ⟨by linarith [(abs_le.mp hr).2], by linarith [(abs_le.mp hr).1]⟩)
  have h2 : ‖((-1 - w.im + a : ℝ) : ℂ) * Complex.I‖ ≤ 6 := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    exact abs_le.mpr ⟨by linarith [(abs_le.mp hi).2], by linarith [(abs_le.mp hi).1]⟩
  exact ((clippedVector_shift_lipschitz w h0 0).add
    (clippedVector_lipschitz h1 1) |>.add (clippedVector_lipschitz h2 2)).weaken (by norm_num)

lemma markedRightRoute_lipschitz {w : ℂ} (hw : ‖w‖ ≤ 1) {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) : LipschitzWith 24 (markedRightRoute w a) := by
  have hr := (Complex.abs_re_le_norm w).trans hw
  have hi := (Complex.abs_im_le_norm w).trans hw
  have h0 : ‖((-a / 2 : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ) * Complex.I‖ ≤ 6 := by
    calc
      _ ≤ |(-a / 2 : ℝ)| + |a / 2| := by simpa using Complex.norm_le_abs_re_add_abs_im (((-a / 2 : ℝ) : ℂ) + ((a / 2 : ℝ) : ℂ) * Complex.I)
      _ ≤ 6 := by rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]; linarith
  have h1 : ‖((2 + a / 2 - w.im : ℝ) : ℂ) * Complex.I‖ ≤ 6 := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    exact abs_le.mpr ⟨by linarith [(abs_le.mp hi).2], by linarith [(abs_le.mp hi).1]⟩
  have h2 : ‖((3 - w.re + a / 2 : ℝ) : ℂ)‖ ≤ 6 := by
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [(abs_le.mp hr).2], by linarith [(abs_le.mp hr).1]⟩
  have h3 : ‖((-3 - a : ℝ) : ℂ) * Complex.I‖ ≤ 6 := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  exact ((clippedVector_shift_lipschitz w h0 0).add
    (clippedVector_lipschitz h1 1) |>.add (clippedVector_lipschitz h2 2) |>.add
    (clippedVector_lipschitz h3 3)).weaken (by norm_num)

end SLEExactGauge.Serpentine

end

end OAI
