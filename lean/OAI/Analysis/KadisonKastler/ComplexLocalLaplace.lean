import OAI.Analysis.KadisonKastler.RealLaplaceUniqueness

namespace OAI

/-! # Complex-valued local Laplace uniqueness -/

namespace KadisonKastler

open MeasureTheory Set

noncomputable section

theorem zero_of_complex_local_laplace (f : ℝ → ℂ) (hf : Continuous f)
    {a : ℝ} (ha : 0 < a)
    (hi : ∀ s ∈ Ioo (-a) a, Integrable (fun t => (Real.exp (s * t) : ℂ) * f t))
    (hz : ∀ s ∈ Ioo (-a) a, (∫ t, (Real.exp (s * t) : ℂ) * f t) = 0) :
    f = 0 := by
  have hre : (fun t => (f t).re) = 0 := zero_of_local_laplace _
    (Complex.continuous_re.comp hf) ha
    (fun s hs => by
      simpa only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero] using (hi s hs).re)
    (fun s hs => by
      have h := integral_re (hi s hs)
      change (∫ t, ((Real.exp (s * t) : ℂ) * f t).re) =
        (∫ t, (Real.exp (s * t) : ℂ) * f t).re at h
      rw [hz s hs] at h
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, Complex.zero_re] using h)
  have him : (fun t => (f t).im) = 0 := zero_of_local_laplace _
    (Complex.continuous_im.comp hf) ha
    (fun s hs => by
      simpa only [RCLike.im_eq_complex_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero] using (hi s hs).im)
    (fun s hs => by
      have h := integral_im (hi s hs)
      change (∫ t, ((Real.exp (s * t) : ℂ) * f t).im) =
        (∫ t, (Real.exp (s * t) : ℂ) * f t).im at h
      rw [hz s hs] at h
      simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, Complex.zero_im] using h)
  funext t
  exact Complex.ext (congrFun hre t) (congrFun him t)

end

end KadisonKastler

end OAI
