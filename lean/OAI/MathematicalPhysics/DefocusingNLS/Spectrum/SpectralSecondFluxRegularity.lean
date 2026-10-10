import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSecondFluxTesting
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicRepresentative
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialLocalIntegrable

namespace OAI

/-! The weak flux is locally integrable and its source has a continuous representative. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable def spectralSecondContinuousSource (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (c ζ : ℂ) (r : ℝ) : ℂ :=
  (((ell : ℝ)*(ell+10) : ℝ) : ℂ)*(r : ℂ)^9*
    (w.density r • spectralHarmonicRepresentative ell R hR u.snd r) +
  (c-ζ)*(r : ℂ)^11*(w.density r • spectralHarmonicRepresentative ell R hR u.fst r)

theorem spectralSecondContinuousSource_continuousOn (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (c ζ : ℂ)
    (hw : ContinuousOn w.density (Ioo 0 R)) :
    ContinuousOn (spectralSecondContinuousSource ell R hR w u c ζ) (Ioo 0 R) := by
  have hf := spectralHarmonicRepresentative_continuousOn ell R hR u.fst
  have hg := spectralHarmonicRepresentative_continuousOn ell R hR u.snd
  exact ((continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.pow 9)).mul
    (hw.smul hg)).add
      ((continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.pow 11)).mul (hw.smul hf))

theorem spectralSecondSource_ae (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (c ζ : ℂ) :
    spectralSecondSource ell R w u c ζ =ᵐ[volume.restrict (Icc 0 R)]
      spectralSecondContinuousSource ell R hR w u c ζ := by
  filter_upwards [spectralHarmonicRepresentative_ae ell R hR u.fst,
    spectralHarmonicRepresentative_ae ell R hR u.snd] with r hf hg
  simp only [spectralSecondSource,spectralSecondContinuousSource,hf,hg]

theorem spectralSecondFlux_locallyIntegrableOn (ell : ℕ) (R : ℝ)
    (w a : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R)
    (hw : ContinuousOn w.density (Ioo 0 R)) (ha : ContinuousOn a.density (Ioo 0 R)) :
    LocallyIntegrableOn (spectralSecondFlux ell R w a u) (Ioo 0 R) := by
  have hd := spectralRadialL2_locallyIntegrableOn R (spectralHarmonicDerivative ell R u.snd)
  have hv := spectralRadialL2_locallyIntegrableOn R (spectralHarmonicValue ell R u.fst)
  have h1 := hd.continuousOn_smul isOpen_Ioo.isLocallyClosed hw
  have h2 := hv.continuousOn_smul isOpen_Ioo.isLocallyClosed ha
  exact (h1.add h2).continuousOn_smul isOpen_Ioo.isLocallyClosed
    (Complex.continuous_ofReal.continuousOn.pow 11)

end DefocusingNLS

end OAI
