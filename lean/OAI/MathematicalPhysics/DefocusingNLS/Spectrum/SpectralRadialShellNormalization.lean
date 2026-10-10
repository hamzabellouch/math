import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialGaugeEnergy

namespace OAI

/-! A unit full radial energy bounds every interior shell used for the
high-frequency boundary argument. -/

open Set MeasureTheory Filter
namespace DefocusingNLS

theorem spectralRadialEnergy_shell_le (eta R B : ℝ) (heta : 0 ≤ eta)
    (hR : 0 ≤ R) (hRB : R ≤ B) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    (∫ r in R..B, spectralPhysicalShellDensity f g r) ≤
      ∫ r in (0 : ℝ)..B, spectralRadialEnergyDensity eta f g r := by
  have hc := spectralPhysicalShellDensity_continuous f g hf hg
  have hd := spectralRadialEnergyDensity_continuous eta f g hf hg
  have hpos : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) B)] spectralPhysicalShellDensity f g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    dsimp only [spectralPhysicalShellDensity]
    have hr0 := hr.1.le
    positivity
  have hs := intervalIntegral.integral_mono_interval hR hRB le_rfl hpos (hc.intervalIntegrable 0 B)
  apply hs.trans
  apply intervalIntegral.integral_mono_on (hR.trans hRB) (hc.intervalIntegrable _ _) (hd.intervalIntegrable _ _)
  intro r hr
  rw [spectralRadialEnergyDensity_eq]
  have hp : 0 ≤ eta*r^9*(‖f r‖^2+‖g r‖^2) := by have hr0 := hr.1; positivity
  linarith

end DefocusingNLS

end OAI
