import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleTransfer

namespace OAI

/-! Choose the WKB orientation from the sign of the real coefficient and the
imaginary constant. Its real action is monotone throughout that interval. -/

open Set
namespace DefocusingNLS

theorem spectralLiouville_orientation (sign h b eta omega gamma R E : ℝ)
    (hs : sign^2=1)
    (hF : ∀ t ∈ Ioo R E, 0<sign*homogeneousSpectralLocalizationFrequency h b eta omega t) :
    ∃ chi : ℂ, ‖chi‖=1 ∧ chi^2*(sign : ℂ)=-1 ∧
      ∀ t ∈ Ioo R E, 0≤(chi*spectralLiouvilleMomentum sign h b eta omega gamma t).re := by
  have hs' : sign=1 ∨ sign=-1 := sq_eq_one_iff.mp hs
  rcases hs' with rfl | rfl
  · by_cases hgamma : gamma≤0
    · refine ⟨Complex.I,Complex.norm_I,by norm_num,?_⟩
      intro t ht
      have hf : 0<homogeneousSpectralLocalizationFrequency h b eta omega t := by
        simpa only [one_mul] using hF t ht
      have hh := (spectralComplexSqrt_im_sign _ gamma hf).2 hgamma
      simpa only [spectralLiouvilleMomentum,spectralWKBSquaredMomentum,Complex.ofReal_one,
        one_mul,Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub] using neg_nonneg.2 hh
    · refine ⟨-Complex.I,by simp only [norm_neg,Complex.norm_I],by norm_num,?_⟩
      intro t ht
      have hf : 0<homogeneousSpectralLocalizationFrequency h b eta omega t := by
        simpa only [one_mul] using hF t ht
      have hh := (spectralComplexSqrt_im_sign _ gamma hf).1 (le_of_not_ge hgamma)
      simpa only [spectralLiouvilleMomentum,spectralWKBSquaredMomentum,Complex.ofReal_one,
        one_mul,Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,
        neg_zero,zero_mul,neg_mul,one_mul,zero_sub,neg_neg] using hh
  · refine ⟨1,by norm_num,by norm_num,?_⟩
    intro t _
    simpa only [one_mul,spectralLiouvilleMomentum] using
      spectralComplexSqrt_re_nonneg (spectralWKBSquaredMomentum (-1)
        (homogeneousSpectralLocalizationFrequency h b eta omega t) gamma)

end DefocusingNLS

end OAI
