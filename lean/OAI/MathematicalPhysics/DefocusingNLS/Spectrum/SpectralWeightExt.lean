import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralComplexMultiplierLimit

namespace OAI

/-! The coefficient multiplier depends only on the density. -/

open MeasureTheory
namespace DefocusingNLS

theorem spectralRadialWeightMultiplier_eq_of_density (R : ℝ)
    (w v : SpectralHarmonicWeight R) (h : w.density=v.density) :
    spectralRadialWeightMultiplier R w=spectralRadialWeightMultiplier R v := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [spectralL2ComplexMultiplier_ae (radialPressureMeasure R) w.density
    w.radial_measurable w.bound w.radial_bound f,
    spectralL2ComplexMultiplier_ae (radialPressureMeasure R) v.density
      v.radial_measurable v.bound v.radial_bound f] with r hw hv
  dsimp only [spectralRadialWeightMultiplier]
  rw [hw,hv,h]

end DefocusingNLS

end OAI
