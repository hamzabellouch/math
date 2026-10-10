import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvillePhaseError
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleTransfer

namespace OAI

/-! Quantitative endpoint transfer for the scalar equation in terms of its
real phase and residual integrals. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralLiouville_endpoint_bound (sign h b eta omega gamma R E A B : ℝ)
    (hs : sign^2=1) (hR : 0<R) (hRE : R≤E) (chi : ℂ) (hchi : ‖chi‖=1)
    (hchi2 : chi^2*(sign : ℂ)=-1)
    (hF : ∀ t ∈ Icc R E, 0<sign*homogeneousSpectralLocalizationFrequency h b eta omega t)
    (hsmall : ∀ t ∈ Icc R E, |spectralLiouvilleSlope eta t|≤
      2*‖spectralLiouvilleMomentum sign h b eta omega gamma t‖^3)
    (hphase : ∀ t ∈ Ioo R E, 0≤(chi*spectralLiouvilleMomentum sign h b eta omega gamma t).re)
    (hA : (∫ t in R..E, 1/Real.sqrt
      (sign*homogeneousSpectralLocalizationFrequency h b eta omega t))≤A)
    (hB : (∫ t in R..E, ‖spectralLiouvilleResidual sign h b eta omega gamma t‖/
      ‖spectralLiouvilleMomentum sign h b eta omega gamma t‖)≤B)
    (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc R E))
    (hODE : ∀ t ∈ Ioo R E, HasDerivAt q
      (spectralScalarField ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+
        Complex.I*(gamma : ℂ)) (q t)) t) :
    spectralShellNorm (Real.sqrt ‖spectralLiouvilleMomentum sign h b eta omega gamma E‖) (q E)≤
      (25/4 : ℝ)*spectralShellNorm
        (Real.sqrt ‖spectralLiouvilleMomentum sign h b eta omega gamma R‖) (q R)*
      Real.exp (chi.re*(∫ t in R..E, Real.sqrt
        (sign*homogeneousSpectralLocalizationFrequency h b eta omega t))+
        |gamma| *A+(25/4)*B) := by
  let p := spectralLiouvilleMomentum sign h b eta omega gamma
  let N := (25/4 : ℝ)*spectralShellNorm (Real.sqrt ‖p R‖) (q R)
  have hN : 0≤N := mul_nonneg (by norm_num)
    (spectralShellNorm_nonneg _ (Real.sqrt_nonneg _) _)
  have ht := spectralLiouville_transfer sign h b eta omega gamma R E hs hR hRE chi hchi
    hchi2 hF hsmall hphase q hq hODE E ⟨hRE,le_rfl⟩
  have hbase : (spectralWKBPhase R chi p R).re=0 := by
    simp only [spectralWKBPhase,intervalIntegral.integral_same,mul_zero,Complex.zero_re]
  have hgap := spectralLiouville_phase_error sign h b eta omega gamma R E hs hR hRE chi hchi hF
  have hphaseB : (spectralWKBPhase R chi p E).re≤
      chi.re*(∫ t in R..E, Real.sqrt
        (sign*homogeneousSpectralLocalizationFrequency h b eta omega t))+|gamma| *A := by
    have hle := le_abs_self ((spectralWKBPhase R chi p E).re-
      chi.re*(∫ t in R..E, Real.sqrt
        (sign*homogeneousSpectralLocalizationFrequency h b eta omega t)))
    have hm := mul_le_mul_of_nonneg_left hA (abs_nonneg gamma)
    linarith
  have he : (∫ t in R..E, (25/4 : ℝ)*‖spectralLiouvilleResidual sign h b eta omega gamma t‖/‖p t‖)=
      (25/4 : ℝ)*(∫ t in R..E, ‖spectralLiouvilleResidual sign h b eta omega gamma t‖/‖p t‖) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    ring
  have hres : (∫ t in R..E, (25/4 : ℝ)*‖spectralLiouvilleResidual sign h b eta omega gamma t‖/‖p t‖)≤
      (25/4 : ℝ)*B := by
    rw [he]
    exact mul_le_mul_of_nonneg_left hB (by norm_num)
  have hexp : (spectralWKBPhase R chi p E).re-(spectralWKBPhase R chi p R).re+
      (∫ t in R..E, (25/4 : ℝ)*‖spectralLiouvilleResidual sign h b eta omega gamma t‖/‖p t‖)≤
      chi.re*(∫ t in R..E, Real.sqrt
        (sign*homogeneousSpectralLocalizationFrequency h b eta omega t))+|gamma| *A+(25/4)*B := by
    rw [hbase,sub_zero]
    exact add_le_add hphaseB hres
  exact ht.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hN)

end DefocusingNLS

end OAI
