import OAI.Analysis.KadisonKastler.StripSineQuotient
import OAI.Analysis.KadisonKastler.StripAverageKernel

namespace OAI

/-! # Boundary values of the regularized strip contour -/

namespace KadisonKastler

noncomputable section

theorem sine_strip_right (t : ℝ) :
    Complex.sin (Real.pi * ((1 / 2 : ℂ) + t * Complex.I)) =
      ((Real.exp (Real.pi * t) + Real.exp (-Real.pi * t) : ℝ) : ℂ) / 2 := by
  rw [show (Real.pi : ℂ) * ((1 / 2 : ℂ) + t * Complex.I) =
    (Real.pi : ℂ) / 2 + (Real.pi * t : ℝ) * Complex.I by push_cast; ring]
  rw [Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two,
    one_mul, zero_mul, add_zero, Complex.cos_mul_I]
  rw [Complex.cosh]
  push_cast
  rw [neg_mul]

theorem sine_strip_left (t : ℝ) :
    Complex.sin (Real.pi * ((-1 / 2 : ℂ) + t * Complex.I)) =
      -(((Real.exp (Real.pi * t) + Real.exp (-Real.pi * t) : ℝ) : ℂ) / 2) := by
  have h := sine_strip_right (-t)
  rw [show (Real.pi : ℂ) * ((-1 / 2 : ℂ) + t * Complex.I) =
    -((Real.pi : ℂ) * ((1 / 2 : ℂ) + (-t : ℝ) * Complex.I)) by push_cast; ring,
    Complex.sin_neg, h]
  congr 2
  push_cast
  simp only [mul_neg, neg_mul, neg_neg]
  ring

theorem stripSineQuotient_right (φ : ℝ) (f : ℂ → ℂ) (t : ℝ) :
    stripSineQuotient φ f ((1 / 2 : ℂ) + t * Complex.I) =
      2 * stripAverageKernel Real.pi (φ : ℂ) t *
        (Complex.exp (Complex.I * φ / 2) * f ((1 / 2 : ℂ) + t * Complex.I)) -
      2 * stripAverageKernel Real.pi 0 t * f 0 := by
  have hz : (1 / 2 : ℂ) + t * Complex.I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
  rw [stripSineQuotient_eq hz, sine_strip_right]
  have he : Complex.I * φ * ((1 / 2 : ℂ) + t * Complex.I) =
      Complex.I * φ / 2 + -((φ : ℂ) * t) := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [he, Complex.exp_add]
  unfold stripAverageKernel
  simp only [zero_mul, neg_zero, Complex.exp_zero]
  ring

theorem stripSineQuotient_left (φ : ℝ) (f : ℂ → ℂ) (t : ℝ) :
    stripSineQuotient φ f ((-1 / 2 : ℂ) + t * Complex.I) =
      -(2 * stripAverageKernel Real.pi (φ : ℂ) t *
        (Complex.exp (-(Complex.I * φ / 2)) * f ((-1 / 2 : ℂ) + t * Complex.I))) +
      2 * stripAverageKernel Real.pi 0 t * f 0 := by
  have hz : (-1 / 2 : ℂ) + t * Complex.I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
  rw [stripSineQuotient_eq hz, sine_strip_left]
  have he : Complex.I * φ * ((-1 / 2 : ℂ) + t * Complex.I) =
      -(Complex.I * φ / 2) + -((φ : ℂ) * t) := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [he, Complex.exp_add]
  unfold stripAverageKernel
  simp only [zero_mul, neg_zero, Complex.exp_zero]
  ring

end

end KadisonKastler

end OAI
