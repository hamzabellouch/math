import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClosedSource

namespace OAI

/-! The positive-radius representative agrees with the completed outer trace. -/

namespace DefocusingNLS

theorem spectralRadialRepresentative_trace (R : ℝ) (hR : 0 < R)
    (u : SpectralRadialEnergy R) :
    spectralRadialRepresentative R hR u R=spectralRadialTrace R hR u := by
  have hnorm : ‖spectralPrimitiveKernel R R hR‖^2=0 := by
    simpa only [intervalIntegral.integral_same] using spectralPrimitiveKernel_norm_sq R R hR le_rfl
  have hz : spectralPrimitiveKernel R R hR=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  rw [spectralRadialRepresentative,dite_eq_left hR]
  change spectralRadialTrace R hR u-inner ℂ (spectralPrimitiveKernel R R hR)
    (spectralRadialDerivative R u)=spectralRadialTrace R hR u
  rw [hz,inner_zero_left,sub_zero]

theorem spectralHarmonicRepresentative_trace (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (u : SpectralHarmonicPair ell R) :
    (spectralHarmonicRepresentative ell R hR u.fst R,
      spectralHarmonicRepresentative ell R hR u.snd R)=spectralHarmonicPairTraces ell R hR u := by
  change (spectralRadialRepresentative R hR (spectralHarmonicRadialForget ell R u.fst) R,
    spectralRadialRepresentative R hR (spectralHarmonicRadialForget ell R u.snd) R)=_
  rw [spectralRadialRepresentative_trace,spectralRadialRepresentative_trace]
  rfl

end DefocusingNLS

end OAI
