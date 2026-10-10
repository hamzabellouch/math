import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeEnergyComparison
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeJetIdentity
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalShellEnergy

namespace OAI

/-! The fixed-ball physical normalization controls the full weighted gauge energy,
including the angular term and the regular origin. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable def spectralRadialEnergyDensity (eta : ℝ) (f g : ℝ → ℂ) (r : ℝ) : ℝ :=
  r^11*(spectralCoordinateEnergy (f r,g r)+spectralCoordinateEnergy (deriv f r,deriv g r))+
    eta*r^9*spectralCoordinateEnergy (f r,g r)

theorem spectralRadialEnergyDensity_eq (eta : ℝ) (f g : ℝ → ℂ) (r : ℝ) :
    spectralRadialEnergyDensity eta f g r = spectralPhysicalShellDensity f g r+
      eta*r^9*(‖f r‖^2+‖g r‖^2) := by
  dsimp only [spectralRadialEnergyDensity,spectralCoordinateEnergy,spectralPhysicalShellDensity]
  ring

theorem spectralRadialEnergyDensity_continuous (eta : ℝ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    Continuous (spectralRadialEnergyDensity eta f g) := by
  have hdf := hf.continuous_deriv (by norm_num)
  have hdg := hg.continuous_deriv (by norm_num)
  change Continuous (fun r : ℝ => r^11*((‖f r‖^2+‖g r‖^2)+
    (‖deriv f r‖^2+‖deriv g r‖^2))+eta*r^9*(‖f r‖^2+‖g r‖^2))
  fun_prop

theorem spectralRadialGaugeEnergy_pointwise (eta c D r : ℝ) (hc : 0 < c)
    (heta : 0 ≤ eta) (hr : 0 ≤ r) (Q f g F G : ℝ → ℂ)
    (hQ : DifferentiableAt ℝ Q r) (hf : DifferentiableAt ℝ f r) (hg : DifferentiableAt ℝ g r)
    (hp : ∀ t, (Q t*(f t+Complex.I*g t),star (Q t)*(f t-Complex.I*g t))=(F t,G t))
    (hm : c ≤ ‖Q r‖^2) (hdQ : ‖deriv Q r‖ ≤ D) :
    ‖Q r‖^2*spectralRadialEnergyDensity eta f g r ≤
      (1+D^2/c)*spectralRadialEnergyDensity eta F G r := by
  obtain ⟨hv,hd⟩ := spectralGauge_jet_identity Q f g F G r hQ hf hg hp
  have h := spectralGauge_weighted_energy_le (Q r) (deriv Q r) (f r,g r)
    (deriv f r,deriv g r) c D (r^11) (eta*r^9) hc hm hdQ (by positivity) (by positivity)
  rw [hv,hd] at h
  dsimp only [spectralRadialEnergyDensity]
  nlinarith only [h]

theorem spectralRadialGaugeEnergy_integral (eta c D R : ℝ) (hc : 0 < c)
    (heta : 0 ≤ eta) (hR : 0 ≤ R) (Q f g F G : ℝ → ℂ)
    (hQ : ContDiff ℝ 2 Q) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G)
    (hp : ∀ t, (Q t*(f t+Complex.I*g t),star (Q t)*(f t-Complex.I*g t))=(F t,G t))
    (hm : ∀ r ∈ Icc 0 R, c ≤ ‖Q r‖^2) (hdQ : ∀ r ∈ Ioc 0 R, ‖deriv Q r‖ ≤ D) :
    (∫ r in (0 : ℝ)..R, ‖Q r‖^2*spectralRadialEnergyDensity eta f g r) ≤
      (1+D^2/c)*(∫ r in (0 : ℝ)..R, spectralRadialEnergyDensity eta F G r) := by
  have hleft := (hQ.continuous.norm.pow 2).mul (spectralRadialEnergyDensity_continuous eta f g hf hg)
  have hright := (spectralRadialEnergyDensity_continuous eta F G hF hG).const_mul (1+D^2/c)
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hR (hleft.intervalIntegrable _ _) (hright.intervalIntegrable _ _)
  intro r hr
  by_cases hz : r=0
  · simp [hz,spectralRadialEnergyDensity]
  · exact spectralRadialGaugeEnergy_pointwise eta c D r hc heta hr.1 Q f g F G
      (hQ.differentiable (by norm_num)).differentiableAt
      (hf.differentiable (by norm_num)).differentiableAt
      (hg.differentiable (by norm_num)).differentiableAt hp (hm r hr)
      (hdQ r ⟨lt_of_le_of_ne hr.1 (Ne.symm hz),hr.2⟩)

theorem spectralGaugeCrossEnergy_le_full (eta r mu : ℝ) (heta : 0 ≤ eta)
    (hr : 0 ≤ r) (hmu : 0 ≤ mu) (f g : ℝ → ℂ) :
    r^11*mu*(‖f r‖^2+‖deriv g r‖^2)+eta*r^9*mu*‖g r‖^2 ≤
      mu*spectralRadialEnergyDensity eta f g r := by
  have h1 : 0 ≤ r^11*mu*‖g r‖^2 := by positivity
  have h2 : 0 ≤ r^11*mu*‖deriv f r‖^2 := by positivity
  have h3 : 0 ≤ eta*r^9*mu*‖f r‖^2 := by positivity
  dsimp only [spectralRadialEnergyDensity,spectralCoordinateEnergy]
  nlinarith only [h1,h2,h3]

theorem spectralGaugeCrossEnergy_integral_le (eta R : ℝ) (heta : 0 ≤ eta) (hR : 0 ≤ R)
    (mu : ℝ → ℝ) (hmu : Continuous mu) (hm : ∀ r ∈ Icc 0 R, 0 ≤ mu r)
    (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    (∫ r in (0 : ℝ)..R, r^11*mu r*(‖f r‖^2+‖deriv g r‖^2)+eta*r^9*mu r*‖g r‖^2) ≤
      ∫ r in (0 : ℝ)..R, mu r*spectralRadialEnergyDensity eta f g r := by
  have hdf := hf.continuous_deriv (by norm_num)
  have hdg := hg.continuous_deriv (by norm_num)
  have hl : Continuous (fun r : ℝ =>
      r^11*mu r*(‖f r‖^2+‖deriv g r‖^2)+eta*r^9*mu r*‖g r‖^2) := by fun_prop
  have hr := hmu.mul (spectralRadialEnergyDensity_continuous eta f g hf hg)
  exact intervalIntegral.integral_mono_on hR (hl.intervalIntegrable _ _) (hr.intervalIntegrable _ _)
    (fun r h => spectralGaugeCrossEnergy_le_full eta r (mu r) heta h.1 (hm r h) f g)

end DefocusingNLS

end OAI
