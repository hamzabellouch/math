import OAI.Probability.SLE.Geometry.MarkedWindowRoutes

namespace OAI

/-! A short initial part of either marked route stays in the free marked
ball, including the entire uniform Brownian tube around that part. -/

noncomputable section
open Set Metric
open scoped Topology

namespace SLEExactGauge.Serpentine
open RibbonCoordinates

lemma markedRoute_initial_dist {w : ℂ} {a u : ℝ} (ha : 0 ≤ a)
    (hu : u ∈ Icc (0 : ℝ) (1 / 48)) :
    dist (markedLeftRoute w a u) w ≤ a / 48 ∧
      dist (markedRightRoute w a u) w ≤ a / 48 := by
  have hleft : markedLeftRoute w a u = w - ((a * u : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;>
      simp only [markedLeftRoute_re, markedLeftRoute_im,
        unitClip_of_mem ⟨hu.1, hu.2.trans (by norm_num)⟩,
        unitClip_of_nonpos (by linarith [hu.2] : u - 1 ≤ 0),
        unitClip_of_nonpos (by linarith [hu.2] : u - 2 ≤ 0),
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, add_zero, sub_zero]
  have hright : markedRightRoute w a u = w + ((-a * u / 2 : ℝ) : ℂ) +
      ((a * u / 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;>
      simp only [markedRightRoute_re, markedRightRoute_im,
        unitClip_of_mem ⟨hu.1, hu.2.trans (by norm_num)⟩,
        unitClip_of_nonpos (by linarith [hu.2] : u - 1 ≤ 0),
        unitClip_of_nonpos (by linarith [hu.2] : u - 2 ≤ 0),
        unitClip_of_nonpos (by linarith [hu.2] : u - 3 ≤ 0),
        Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, add_zero, sub_zero] <;> ring
  have hprod : 0 ≤ a * u := mul_nonneg ha hu.1
  have hbound : a * u ≤ a / 48 := by nlinarith [hu.2]
  constructor
  · rw [hleft, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one, abs_of_nonneg hprod]
    exact hbound
  · rw [hright, dist_eq_norm]
    have he : w + ((-a * u / 2 : ℝ) : ℂ) + ((a * u / 2 : ℝ) : ℂ) * Complex.I - w =
        ((-a * u / 2 : ℝ) : ℂ) + ((a * u / 2 : ℝ) : ℂ) * Complex.I := by ring
    rw [he]
    calc
      _ ≤ |(-a * u / 2 : ℝ)| + |a * u / 2| := by
        simpa using Complex.norm_le_abs_re_add_abs_im
          (((-a * u / 2 : ℝ) : ℂ) + ((a * u / 2 : ℝ) : ℂ) * Complex.I)
      _ = a * u := by rw [abs_of_nonpos (by nlinarith), abs_of_nonneg (by positivity)]; ring
      _ ≤ a / 48 := hbound

lemma markedWindowRoute_early_dist (right : Bool) (w : ℂ) {a : ℝ} (ha : 0 ≤ a)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 64)) :
    dist (markedWindowRoute right w a t) w ≤ a / 48 := by
  have hu : 4 / 3 * t ∈ Icc (0 : ℝ) (1 / 48) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  cases right
  · exact (markedRoute_initial_dist ha hu).1
  · exact (markedRoute_initial_dist ha hu).2

end SLEExactGauge.Serpentine

end

end OAI
