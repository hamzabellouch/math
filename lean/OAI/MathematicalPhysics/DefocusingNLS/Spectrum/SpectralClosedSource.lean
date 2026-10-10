import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSecondFluxRegularity

namespace OAI

/-! The source of the scalar flux equation is continuous through the finite endpoint. -/

open Set
namespace DefocusingNLS

theorem spectralHarmonicRepresentative_continuousOn_closed (ell : ℕ) (R a : ℝ)
    (hR : 0 < R) (ha : 0 < a) (u : SpectralHarmonicEnergy ell R) :
    ContinuousOn (spectralHarmonicRepresentative ell R hR u) (Icc a R) :=
  spectralRadialRepresentative_continuousOn R a hR ha (spectralHarmonicRadialForget ell R u)

theorem spectralSecondContinuousSource_closed (ell : ℕ) (R a : ℝ) (hR : 0 < R)
    (ha : 0 < a) (w : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R)
    (c ζ : ℂ) (hw : ContinuousOn w.density (Icc a R)) :
    ContinuousOn (spectralSecondContinuousSource ell R hR w u c ζ) (Icc a R) := by
  have hf := spectralHarmonicRepresentative_continuousOn_closed ell R a hR ha u.fst
  have hg := spectralHarmonicRepresentative_continuousOn_closed ell R a hR ha u.snd
  exact ((continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.pow 9)).mul
    (hw.smul hg)).add
      ((continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.pow 11)).mul (hw.smul hf))

end DefocusingNLS

end OAI
