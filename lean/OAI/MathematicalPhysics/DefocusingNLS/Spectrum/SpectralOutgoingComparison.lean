import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarReflection
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOscillatoryWeight
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleFrequencyJet

namespace OAI

/-! The scalar outgoing comparison solution is constructed from its exact
remote Cauchy data, including the normalized flux and size. -/

open Set
namespace DefocusingNLS

theorem spectralLiouville_outgoing_exists (h b eta omega gamma R E : ℝ)
    (hh : h^2=1) (hR : 0<R) (hRE : R≤E)
    (hF : 0<homogeneousSpectralLocalizationFrequency h b eta omega E)
    (hgamma : |gamma|≤homogeneousSpectralLocalizationFrequency h b eta omega E) :
    ∃ q : ℝ → ℂ × ℂ, Continuous q ∧
      q E=spectralOscillatoryData h
        (Real.sqrt (Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega E))) ∧
      spectralScalarFlux (q E)=h ∧
      spectralShellNorm (Real.sqrt ‖spectralLiouvilleMomentum 1 h b eta omega gamma E‖) (q E)≤3 ∧
      ∀ t ∈ Icc R E, HasDerivAt q
        (spectralScalarField ((homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+
          Complex.I*(gamma : ℂ)) (q t)) t := by
  let V := fun t => (homogeneousSpectralLocalizationFrequency h b eta omega t : ℂ)+Complex.I*(gamma : ℂ)
  let k := Real.sqrt (Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega E))
  have hk : 0<k := Real.sqrt_pos.2 (Real.sqrt_pos.2 hF)
  have hV : ContinuousOn V (Icc R E) := by
    apply ContinuousOn.add _ continuousOn_const
    apply Complex.continuous_ofReal.comp_continuousOn
    intro t ht
    exact (homogeneousSpectralLocalizationFrequency_hasDerivAt h b eta omega t
      (hR.trans_le ht.1)).continuousAt.continuousWithinAt
  obtain ⟨q,hq,hqE,hqD⟩ := spectralScalar_terminal_exists R E hRE V hV (spectralOscillatoryData h k)
  refine ⟨q,hq,hqE,?_,?_,hqD⟩
  · rw [hqE]
    exact spectralOscillatoryData_flux h k hk.ne'
  · rw [hqE]
    simpa only [spectralLiouvilleMomentum,spectralWKBSquaredMomentum,Complex.ofReal_one,one_mul] using
      spectralOscillatoryData_complex_norm h
        (homogeneousSpectralLocalizationFrequency h b eta omega E) gamma hh hF hgamma

end DefocusingNLS

end OAI
