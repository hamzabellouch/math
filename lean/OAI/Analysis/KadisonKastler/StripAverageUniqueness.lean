import OAI.Analysis.KadisonKastler.RealLaplaceUniqueness
import OAI.Analysis.KadisonKastler.StripAverageKernel

namespace OAI

/-! # The modular averaging kernels separate bounded continuous functions -/

namespace KadisonKastler

open MeasureTheory Set

noncomputable section

theorem stripAverageKernel_tilt (a s t : ℝ) :
    (Real.exp (s * t) : ℂ) * stripAverageKernel a 0 t =
      stripAverageKernel a (-s : ℂ) t := by
  unfold stripAverageKernel
  rw [zero_mul, neg_zero, Complex.exp_zero, Complex.ofReal_exp]
  push_cast
  simp only [neg_mul, neg_neg, div_eq_mul_inv, one_mul]

theorem stripAverageKernel_ne_zero (a t : ℝ) : stripAverageKernel a 0 t ≠ 0 := by
  unfold stripAverageKernel
  apply div_ne_zero (Complex.exp_ne_zero _)
  exact_mod_cast (add_pos (Real.exp_pos (a * t)) (Real.exp_pos (-a * t))).ne'

/-- A bounded continuous coefficient is determined by all the real exponential
tilts of the strip averaging kernel. -/
theorem zero_of_strip_averages {a : ℝ} (ha : 0 < a) (g : ℝ → ℂ)
    (hg : Continuous g) {B : ℝ} (hB : ∀ t, ‖g t‖ ≤ B)
    (hz : ∀ s ∈ Ioo (-a) a, (∫ t, stripAverageKernel a (s : ℂ) t * g t) = 0) :
    g = 0 := by
  let f : ℝ → ℂ := fun t => stripAverageKernel a 0 t * g t
  have hfc : Continuous f := (stripAverageKernel_continuous a 0).mul hg
  have hint (s : ℝ) (hs : s ∈ Ioo (-a) a) :
      Integrable (fun t => (Real.exp (s * t) : ℂ) * f t) := by
    have hh : |(-s : ℂ).re| < a := by
      simp only [Complex.neg_re, Complex.ofReal_re, abs_neg]
      exact abs_lt.mpr hs
    have hi := (stripAverageKernel_integrable hh).mul_bdd hg.aestronglyMeasurable
      (Filter.Eventually.of_forall hB)
    convert hi using 1
    funext t
    change (Real.exp (s * t) : ℂ) * (stripAverageKernel a 0 t * g t) = _
    rw [← mul_assoc, stripAverageKernel_tilt]
  have hzero (s : ℝ) (hs : s ∈ Ioo (-a) a) :
      (∫ t, (Real.exp (s * t) : ℂ) * f t) = 0 := by
    have he : (fun t => (Real.exp (s * t) : ℂ) * f t) =
        (fun t => stripAverageKernel a (-s : ℂ) t * g t) := by
      funext t
      change (Real.exp (s * t) : ℂ) * (stripAverageKernel a 0 t * g t) = _
      rw [← mul_assoc, stripAverageKernel_tilt]
    rw [he]
    simpa only [Complex.ofReal_neg] using
      hz (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hre : (fun t => (f t).re) = 0 := zero_of_local_laplace _
    (Complex.continuous_re.comp hfc) ha
    (fun s hs => by
      simpa only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        using (hint s hs).re)
    (fun s hs => by
      have h := integral_re (hint s hs)
      change (∫ t, ((Real.exp (s * t) : ℂ) * f t).re) =
        (∫ t, (Real.exp (s * t) : ℂ) * f t).re at h
      rw [hzero s hs] at h
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.zero_re] using h)
  have him : (fun t => (f t).im) = 0 := zero_of_local_laplace _
    (Complex.continuous_im.comp hfc) ha
    (fun s hs => by
      simpa only [RCLike.im_eq_complex_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
        using (hint s hs).im)
    (fun s hs => by
      have h := integral_im (hint s hs)
      change (∫ t, ((Real.exp (s * t) : ℂ) * f t).im) =
        (∫ t, (Real.exp (s * t) : ℂ) * f t).im at h
      rw [hzero s hs] at h
      simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
        Complex.zero_im] using h)
  funext t
  have hf0 : f t = 0 := Complex.ext (congrFun hre t) (congrFun him t)
  exact (mul_eq_zero.mp hf0).resolve_left (stripAverageKernel_ne_zero a t)

end

end KadisonKastler

end OAI
