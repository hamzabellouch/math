import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarReverseTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleNormPositive

namespace OAI

/-! Both directions of the actual forbidden scalar evolution have the same
complex-action bound. The reverse estimate follows from conserved Wronskians. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralLiouville_forbidden_endpoint (h b eta omega gamma R E : ℝ)
    (hR : 0 < R) (hRE : R ≤ E)
    (hF : ∀ t ∈ Icc R E, 0 < (-1)*homogeneousSpectralLocalizationFrequency h b eta omega t)
    (hsmall : ∀ t ∈ Icc R E, |spectralLiouvilleSlope eta t| ≤
      2*‖spectralLiouvilleMomentum (-1) h b eta omega gamma t‖^3)
    (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc R E))
    (hODE : ∀ t ∈ Ioo R E, HasDerivAt q
      (spectralScalarField ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+
        Complex.I*(gamma : ℂ)) (q t)) t) :
    let p := spectralLiouvilleMomentum (-1) h b eta omega gamma
    let k := fun t => Real.sqrt ‖p t‖
    let J := ∫ t in R..E, (25/4 : ℝ)*‖spectralLiouvilleResidual (-1) h b eta omega gamma t‖/‖p t‖
    let C := (25/4 : ℝ)*Real.exp ((∫ t in R..E, p t).re+J)
    spectralShellNorm (k E) (q E) ≤ C*spectralShellNorm (k R) (q R) ∧
      spectralShellNorm (k R) (q R) ≤ (2*C)*spectralShellNorm (k E) (q E) := by
  dsimp only
  let p := spectralLiouvilleMomentum (-1) h b eta omega gamma
  let k := fun t => Real.sqrt ‖p t‖
  let V := fun t => (homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+Complex.I*(gamma : ℂ)
  let J := ∫ t in R..E, (25/4 : ℝ)*‖spectralLiouvilleResidual (-1) h b eta omega gamma t‖/‖p t‖
  let C := (25/4 : ℝ)*Real.exp ((∫ t in R..E, p t).re+J)
  have hk (t : ℝ) (ht : t ∈ Icc R E) : 0 < k t :=
    spectralLiouville_norm_weight_pos (-1) h b eta omega gamma t (by norm_num)
      (by intro he; have hf := hF t ht; rw [he,mul_zero] at hf; linarith)
  have hV : ContinuousOn V (Icc R E) :=
    (Complex.continuous_ofReal.comp_continuousOn (fun t ht =>
      (homogeneousSpectralLocalizationFrequency_hasDerivAt h b eta omega t
        (hR.trans_le ht.1)).continuousAt.continuousWithinAt)).add continuousOn_const
  have hfwd (u : ℝ → ℂ × ℂ) (hu : ContinuousOn u (Icc R E))
      (huD : ∀ t ∈ Ioo R E, HasDerivAt u (spectralScalarField (V t) (u t)) t) :
      spectralShellNorm (k E) (u E) ≤ C*spectralShellNorm (k R) (u R) := by
    have ht := spectralLiouville_transfer (-1) h b eta omega gamma R E
      (by norm_num) hR hRE 1 (by norm_num) (by norm_num) hF hsmall
      (fun t _ => by
        simpa only [one_mul,spectralLiouvilleMomentum] using spectralComplexSqrt_re_nonneg
          (spectralWKBSquaredMomentum (-1) (homogeneousSpectralLocalizationFrequency h b eta omega t) gamma))
      u hu huD E ⟨hRE,le_rfl⟩
    simp only [spectralWKBPhase,one_mul,intervalIntegral.integral_same,
      Complex.zero_re,sub_zero] at ht
    convert ht using 1
    dsimp only [C,J,p,k]
    ring
  exact ⟨hfwd q hq hODE,spectralScalar_reverse_transfer R E (k R) (k E) C hRE
    (hk R ⟨le_rfl,hRE⟩) (hk E ⟨hRE,le_rfl⟩) V hV hfwd q hq hODE⟩

end DefocusingNLS

end OAI
