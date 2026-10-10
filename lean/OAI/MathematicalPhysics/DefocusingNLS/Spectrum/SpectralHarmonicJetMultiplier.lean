import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicForm
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralL2ComplexMultiplier

namespace OAI

/-! Multiplication and the product rule on the ambient harmonic jet space. -/

namespace DefocusingNLS

noncomputable def spectralHarmonicJetMultiplier (R : ℝ) (w d : SpectralHarmonicWeight R) :
    SpectralHarmonicJet R →L[ℂ] SpectralHarmonicJet R :=
  let X := WithLp.fstL 2 ℂ (SpectralRadialJetSpace R) (SpectralAngularL2 R)
  let V := (WithLp.fstL 2 ℂ (SpectralRadialL2 R) (SpectralRadialL2 R)).comp X
  let D := (WithLp.sndL 2 ℂ (SpectralRadialL2 R) (SpectralRadialL2 R)).comp X
  let G := WithLp.sndL 2 ℂ (SpectralRadialJetSpace R) (SpectralAngularL2 R)
  let P := spectralL2ComplexMultiplier (radialPressureMeasure R) w.density
    w.radial_measurable w.bound w.radial_bound
  let Pd := spectralL2ComplexMultiplier (radialPressureMeasure R) d.density
    d.radial_measurable d.bound d.radial_bound
  let Pa := spectralL2ComplexMultiplier (spectralAngularMeasure R) w.density
    w.angular_measurable w.bound w.angular_bound
  let J := (WithLp.prodContinuousLinearEquiv 2 ℂ (SpectralRadialL2 R)
    (SpectralRadialL2 R)).symm.toContinuousLinearMap.comp
      ((P.comp V).prod ((Pd.comp V)+(P.comp D)))
  (WithLp.prodContinuousLinearEquiv 2 ℂ (SpectralRadialJetSpace R)
    (SpectralAngularL2 R)).symm.toContinuousLinearMap.comp (J.prod (Pa.comp G))

theorem spectralHarmonicJetMultiplier_value (R : ℝ) (w d : SpectralHarmonicWeight R)
    (u : SpectralHarmonicJet R) :
    (spectralHarmonicJetMultiplier R w d u).fst.fst=
      spectralL2ComplexMultiplier (radialPressureMeasure R) w.density
        w.radial_measurable w.bound w.radial_bound u.fst.fst := rfl

theorem spectralHarmonicJetMultiplier_derivative (R : ℝ) (w d : SpectralHarmonicWeight R)
    (u : SpectralHarmonicJet R) :
    (spectralHarmonicJetMultiplier R w d u).fst.snd=
      spectralL2ComplexMultiplier (radialPressureMeasure R) d.density
        d.radial_measurable d.bound d.radial_bound u.fst.fst+
      spectralL2ComplexMultiplier (radialPressureMeasure R) w.density
        w.radial_measurable w.bound w.radial_bound u.fst.snd := rfl

theorem spectralHarmonicJetMultiplier_angular (R : ℝ) (w d : SpectralHarmonicWeight R)
    (u : SpectralHarmonicJet R) :
    (spectralHarmonicJetMultiplier R w d u).snd=
      spectralL2ComplexMultiplier (spectralAngularMeasure R) w.density
        w.angular_measurable w.bound w.angular_bound u.snd := rfl

end DefocusingNLS

end OAI
