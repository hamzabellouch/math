import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialGaugeEnergy

namespace OAI

/-! Each value or radial derivative in the second component is controlled
by the full nonnegative gauge energy. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralGauge_second_component_energy_le (eta R : ℝ) (he : 0 ≤ eta) (hR : 0 ≤ R)
    (mu : ℝ → ℝ) (hmu : Continuous mu) (hm : ∀ r ∈ Icc 0 R, 0 ≤ mu r)
    (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    (∫ r in (0 : ℝ)..R, r^11*mu r*‖g r‖^2) ≤
      (∫ r in (0 : ℝ)..R, mu r*spectralRadialEnergyDensity eta f g r) ∧
    (∫ r in (0 : ℝ)..R, r^11*mu r*‖deriv g r‖^2) ≤
      (∫ r in (0 : ℝ)..R, mu r*spectralRadialEnergyDensity eta f g r) := by
  have hc := hmu.mul (spectralRadialEnergyDensity_continuous eta f g hf hg)
  have hdg := hg.continuous_deriv (by norm_num)
  have hpoint r (hr : r ∈ Icc 0 R) :
      r^11*mu r*‖g r‖^2 ≤ mu r*spectralRadialEnergyDensity eta f g r ∧
      r^11*mu r*‖deriv g r‖^2 ≤ mu r*spectralRadialEnergyDensity eta f g r := by
    have h1 : 0 ≤ r^11*mu r*‖f r‖^2 := by have := hr.1; have := hm r hr; positivity
    have h2 : 0 ≤ r^11*mu r*‖g r‖^2 := by have := hr.1; have := hm r hr; positivity
    have h3 : 0 ≤ r^11*mu r*‖deriv f r‖^2 := by have := hr.1; have := hm r hr; positivity
    have h4 : 0 ≤ r^11*mu r*‖deriv g r‖^2 := by have := hr.1; have := hm r hr; positivity
    have h5 : 0 ≤ eta*r^9*mu r*(‖f r‖^2+‖g r‖^2) := by have := hr.1; have := hm r hr; positivity
    dsimp only [spectralRadialEnergyDensity,spectralCoordinateEnergy]
    constructor <;> nlinarith only [h1,h2,h3,h4,h5]
  constructor
  · apply intervalIntegral.integral_mono_on hR _ (hc.intervalIntegrable 0 R)
      (fun r hr => (hpoint r hr).1)
    exact ((((continuous_id.pow 11).mul hmu).mul (hg.continuous.norm.pow 2)).intervalIntegrable 0 R)
  · apply intervalIntegral.integral_mono_on hR _ (hc.intervalIntegrable 0 R)
      (fun r hr => (hpoint r hr).2)
    exact ((((continuous_id.pow 11).mul hmu).mul (hdg.norm.pow 2)).intervalIntegrable 0 R)

end DefocusingNLS

end OAI
