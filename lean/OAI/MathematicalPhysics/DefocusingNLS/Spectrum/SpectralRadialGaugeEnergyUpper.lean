import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialGaugeEnergy

namespace OAI

/-! The reverse norm comparison transfers vanishing gauge H1/angular energy
back to the physical normalization. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralGauge_weighted_energy_upper (Q dQ : ℂ) (x dx : ℂ × ℂ) (c D w v : ℝ)
    (hc : 0 < c) (hm : c ≤ ‖Q‖^2) (hdQ : ‖dQ‖ ≤ D) (hw : 0 ≤ w) (hv : 0 ≤ v) :
    w*(spectralCoordinateEnergy (spectralGaugeColumns Q x)+
        spectralCoordinateEnergy (spectralGaugeColumns Q dx+spectralGaugeColumns dQ x))+
        v*spectralCoordinateEnergy (spectralGaugeColumns Q x) ≤
      (4+4*D^2/c)*(w*‖Q‖^2*(spectralCoordinateEnergy x+spectralCoordinateEnergy dx)+
        v*‖Q‖^2*spectralCoordinateEnergy x) := by
  have hbase := (spectralGauge_energy_comparison Q dQ x dx c D 0 hc hm hdQ le_rfl).1
  simp only [add_zero,one_mul] at hbase
  have hvalue : spectralCoordinateEnergy (spectralGaugeColumns Q x) ≤
      (4+4*D^2/c)*‖Q‖^2*spectralCoordinateEnergy x := by
    rw [spectralGaugeColumns_energy]
    have hp : 0 ≤ ‖Q‖^2*spectralCoordinateEnergy x :=
      mul_nonneg (sq_nonneg _) (spectralCoordinateEnergy_nonneg _)
    have hk : 0 ≤ 4*D^2/c := by positivity
    nlinarith only [hp,mul_nonneg hk hp]
  have h1 := mul_le_mul_of_nonneg_left hbase hw
  have h2 := mul_le_mul_of_nonneg_left hvalue hv
  nlinarith only [h1,h2]

theorem spectralRadialGaugeEnergy_upper_pointwise (eta c D r : ℝ) (hc : 0 < c)
    (heta : 0 ≤ eta) (hr : 0 ≤ r) (Q f g F G : ℝ → ℂ)
    (hQ : DifferentiableAt ℝ Q r) (hf : DifferentiableAt ℝ f r) (hg : DifferentiableAt ℝ g r)
    (hp : ∀ t, (Q t*(f t+Complex.I*g t),star (Q t)*(f t-Complex.I*g t))=(F t,G t))
    (hm : c ≤ ‖Q r‖^2) (hdQ : ‖deriv Q r‖ ≤ D) :
    spectralRadialEnergyDensity eta F G r ≤
      (4+4*D^2/c)*(‖Q r‖^2*spectralRadialEnergyDensity eta f g r) := by
  obtain ⟨hv,hd⟩ := spectralGauge_jet_identity Q f g F G r hQ hf hg hp
  have h := spectralGauge_weighted_energy_upper (Q r) (deriv Q r) (f r,g r)
    (deriv f r,deriv g r) c D (r^11) (eta*r^9) hc hm hdQ (by positivity) (by positivity)
  rw [hv,hd] at h
  dsimp only [spectralRadialEnergyDensity]
  nlinarith only [h]

theorem spectralRadialGaugeEnergy_upper_integral (eta c D R : ℝ) (hc : 0 < c)
    (heta : 0 ≤ eta) (hR : 0 ≤ R) (Q f g F G : ℝ → ℂ)
    (hQ : ContDiff ℝ 2 Q) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G)
    (hp : ∀ t, (Q t*(f t+Complex.I*g t),star (Q t)*(f t-Complex.I*g t))=(F t,G t))
    (hm : ∀ r ∈ Icc 0 R, c ≤ ‖Q r‖^2) (hdQ : ∀ r ∈ Ioc 0 R, ‖deriv Q r‖ ≤ D) :
    (∫ r in (0 : ℝ)..R, spectralRadialEnergyDensity eta F G r) ≤
      (4+4*D^2/c)*(∫ r in (0 : ℝ)..R, ‖Q r‖^2*spectralRadialEnergyDensity eta f g r) := by
  have hleft := spectralRadialEnergyDensity_continuous eta F G hF hG
  have hright := (hQ.continuous.norm.pow 2).mul (spectralRadialEnergyDensity_continuous eta f g hf hg)
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on hR (hleft.intervalIntegrable _ _) ((hright.const_mul _).intervalIntegrable _ _)
  intro r hr
  by_cases hz : r=0
  · simp [hz,spectralRadialEnergyDensity]
  · exact spectralRadialGaugeEnergy_upper_pointwise eta c D r hc heta hr.1 Q f g F G
      (hQ.differentiable (by norm_num)).differentiableAt
      (hf.differentiable (by norm_num)).differentiableAt
      (hg.differentiable (by norm_num)).differentiableAt hp (hm r hr)
      (hdQ r ⟨lt_of_le_of_ne hr.1 (Ne.symm hz),hr.2⟩)

end DefocusingNLS

end OAI
