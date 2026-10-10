import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicObservation
import Mathlib.MeasureTheory.Measure.SeparableMeasure

namespace OAI

/-! Separable fixed-harmonic form domains, with the intermediate topology
instances exhibited so typeclass search need not traverse the full jet tower. -/

open MeasureTheory
open scoped ENNReal
namespace DefocusingNLS

theorem spectralHarmonicPair_separable (ell : ℕ) (R : ℝ) :
    TopologicalSpace.SeparableSpace (SpectralHarmonicPair ell R) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : IsSeparable (radialPressureMeasure R) := inferInstance
  let : IsSeparable (spectralAngularMeasure R) := inferInstance
  let : SecondCountableTopology (SpectralRadialL2 R) := inferInstance
  let : SecondCountableTopology (SpectralAngularL2 R) := inferInstance
  let : SecondCountableTopology (SpectralRadialJetSpace R) := inferInstance
  let : SecondCountableTopology (SpectralHarmonicJet R) := inferInstance
  let : SecondCountableTopology (SpectralHarmonicEnergy ell R) := inferInstance
  let : SecondCountableTopology (SpectralHarmonicPair ell R) := inferInstance
  infer_instance

end DefocusingNLS

end OAI
