import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleEndpoint
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleOrientation
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarReverseTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleNormPositive

namespace OAI

/-! Oscillatory transfer is controlled by the real phase-error integral and
the WKB residual. Both directions use the same finite constant. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralLiouville_oscillatory_endpoint (h b eta omega gamma R E A B : ℝ)
    (hR : 0 < R) (hRE : R ≤ E)
    (hF : ∀ t ∈ Icc R E, 0 < homogeneousSpectralLocalizationFrequency h b eta omega t)
    (hsmall : ∀ t ∈ Icc R E, |spectralLiouvilleSlope eta t| ≤
      2*‖spectralLiouvilleMomentum 1 h b eta omega gamma t‖^3)
    (hA : (∫ t in R..E, 1/Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega t)) ≤ A)
    (hB : (∫ t in R..E, ‖spectralLiouvilleResidual 1 h b eta omega gamma t‖/
      ‖spectralLiouvilleMomentum 1 h b eta omega gamma t‖) ≤ B)
    (q : ℝ → ℂ × ℂ) (hq : ContinuousOn q (Icc R E))
    (hODE : ∀ t ∈ Ioo R E, HasDerivAt q
      (spectralScalarField ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+
        Complex.I*(gamma : ℂ)) (q t)) t) :
    let k := fun t => Real.sqrt ‖spectralLiouvilleMomentum 1 h b eta omega gamma t‖
    let C := (25/4 : ℝ)*Real.exp (|gamma| *A+(25/4)*B)
    spectralShellNorm (k E) (q E) ≤ C*spectralShellNorm (k R) (q R) ∧
      spectralShellNorm (k R) (q R) ≤ (2*C)*spectralShellNorm (k E) (q E) := by
  dsimp only
  let k := fun t => Real.sqrt ‖spectralLiouvilleMomentum 1 h b eta omega gamma t‖
  let V := fun t => (homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+Complex.I*(gamma : ℂ)
  let C := (25/4 : ℝ)*Real.exp (|gamma| *A+(25/4)*B)
  have hF' (t : ℝ) (ht : t ∈ Icc R E) :
      0 < 1*homogeneousSpectralLocalizationFrequency h b eta omega t := by simpa only [one_mul] using hF t ht
  obtain ⟨chi,hchi,hchi2,hphase⟩ := spectralLiouville_orientation 1 h b eta omega gamma R E
    (by norm_num) (fun t ht => hF' t ⟨ht.1.le,ht.2.le⟩)
  have hchiRe : chi.re = 0 := by
    have hc2 : chi^2 = Complex.I^2 := by simpa only [Complex.ofReal_one,mul_one,Complex.I_sq] using hchi2
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hc2 with hc | hc
    · simp only [hc,Complex.I_re]
    · simp only [hc,Complex.neg_re,Complex.I_re,neg_zero]
  have hkp (t : ℝ) (ht : t ∈ Icc R E) : 0 < k t :=
    spectralLiouville_norm_weight_pos 1 h b eta omega gamma t (by norm_num) (hF t ht).ne'
  have hV : ContinuousOn V (Icc R E) :=
    (Complex.continuous_ofReal.comp_continuousOn (fun t ht =>
      (homogeneousSpectralLocalizationFrequency_hasDerivAt h b eta omega t
        (hR.trans_le ht.1)).continuousAt.continuousWithinAt)).add continuousOn_const
  have hfwd (u : ℝ → ℂ × ℂ) (hu : ContinuousOn u (Icc R E))
      (huD : ∀ t ∈ Ioo R E, HasDerivAt u (spectralScalarField (V t) (u t)) t) :
      spectralShellNorm (k E) (u E) ≤ C*spectralShellNorm (k R) (u R) := by
    have ht := spectralLiouville_endpoint_bound 1 h b eta omega gamma R E A B
      (by norm_num) hR hRE chi hchi hchi2 hF' hsmall hphase
      (by simpa only [one_mul] using hA) hB u hu huD
    simp only [hchiRe,zero_mul,zero_add] at ht
    convert ht using 1
    dsimp only [C]
    ring
  exact ⟨hfwd q hq hODE,spectralScalar_reverse_transfer R E (k R) (k E) C hRE
    (hkp R ⟨le_rfl,hRE⟩) (hkp E ⟨hRE,le_rfl⟩) V hV hfwd q hq hODE⟩

end DefocusingNLS

end OAI
