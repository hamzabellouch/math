import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicForm
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralL2ComplexMultiplier
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralComplexLinear

namespace OAI

/-! Compatibility of the complete harmonic form with multiplication by i. -/

namespace DefocusingNLS

theorem spectralHarmonicForm_I (ell : ℕ) (R : ℝ) (w : SpectralHarmonicWeight R)
    (u v : SpectralHarmonicEnergy ell R) :
    spectralHarmonicForm ell R w (Complex.I • u) v =
      -spectralHarmonicForm ell R w u (Complex.I • v) := by
  let V := (spectralRadialValue R).comp (spectralHarmonicRadialForget ell R)
  let D := (spectralRadialDerivative R).comp (spectralHarmonicRadialForget ell R)
  let G := spectralHarmonicAngularValue ell R
  let P := spectralL2ComplexMultiplier (radialPressureMeasure R) w.density
    w.radial_measurable w.bound w.radial_bound
  let A := spectralL2ComplexMultiplier (spectralAngularMeasure R) w.density
    w.angular_measurable w.bound w.angular_bound
  change inner ℝ (P (V (Complex.I • u))) (V v)+
      inner ℝ (P (D (Complex.I • u))) (D v)+inner ℝ (A (G (Complex.I • u))) (G v)=
    -(inner ℝ (P (V u)) (V (Complex.I • v))+
      inner ℝ (P (D u)) (D (Complex.I • v))+inner ℝ (A (G u)) (G (Complex.I • v)))
  simp only [map_smul,spectralCompatibleInner_I]
  ring

theorem spectralHarmonicPairForm_I (ell : ℕ) (R : ℝ) (w : SpectralHarmonicWeight R)
    (u v : SpectralHarmonicPair ell R) :
    spectralHarmonicPairForm ell R w (Complex.I • u) v =
      -spectralHarmonicPairForm ell R w u (Complex.I • v) := by
  change spectralHarmonicForm ell R w (Complex.I • u.fst) v.fst+
      spectralHarmonicForm ell R w (Complex.I • u.snd) v.snd=
    -(spectralHarmonicForm ell R w u.fst (Complex.I • v.fst)+
      spectralHarmonicForm ell R w u.snd (Complex.I • v.snd))
  rw [spectralHarmonicForm_I,spectralHarmonicForm_I]
  ring

end DefocusingNLS

end OAI
