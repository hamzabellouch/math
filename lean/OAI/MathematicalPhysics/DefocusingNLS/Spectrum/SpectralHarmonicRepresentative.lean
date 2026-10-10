import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialOpenContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicCoordinates

namespace OAI

/-! Continuous positive-radius representatives of the completed harmonic coordinates. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable def spectralHarmonicRepresentative (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (u : SpectralHarmonicEnergy ell R) : ℝ → ℂ :=
  spectralRadialRepresentative R hR (spectralHarmonicRadialForget ell R u)

theorem spectralHarmonicRepresentative_continuousOn (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (u : SpectralHarmonicEnergy ell R) :
    ContinuousOn (spectralHarmonicRepresentative ell R hR u) (Ioo 0 R) :=
  spectralRadialRepresentative_continuousOn_open R hR _

theorem spectralHarmonicRepresentative_ae (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (u : SpectralHarmonicEnergy ell R) :
    spectralHarmonicRepresentative ell R hR u =ᵐ[volume.restrict (Icc 0 R)]
      spectralHarmonicValue ell R u :=
  (spectralRadialVolume_absolutelyContinuous R).ae_le
    (spectralRadialRepresentative_ae R hR (spectralHarmonicRadialForget ell R u))

end DefocusingNLS

end OAI
