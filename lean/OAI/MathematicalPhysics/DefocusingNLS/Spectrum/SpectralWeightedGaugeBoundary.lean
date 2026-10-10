import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleWeightedEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialGaugeEnergy

namespace OAI

/-! Fixed-radius gauge changes preserve vanishing frequency-weighted Cauchy
energy under a positive mass bound and a bounded profile derivative. -/

namespace DefocusingNLS

theorem spectralWeightedGaugeBoundary_le (omega c D r : ℝ) (ho : 1 ≤ omega) (hc : 0 < c)
    (Q f g F G : ℝ → ℂ) (hQ : DifferentiableAt ℝ Q r)
    (hf : DifferentiableAt ℝ f r) (hg : DifferentiableAt ℝ g r)
    (hp : ∀ t, (Q t*(f t+Complex.I*g t),star (Q t)*(f t-Complex.I*g t))=(F t,G t))
    (hm : c ≤ ‖Q r‖^2) (hdQ : ‖deriv Q r‖ ≤ D) :
    ‖Q r‖^2*spectralWeightedCauchyEnergy omega f g r ≤
      (1+D^2/c)*spectralWeightedCauchyEnergy omega F G r := by
  obtain ⟨hv,hd⟩ := spectralGauge_jet_identity Q f g F G r hQ hf hg hp
  have hb := (spectralGauge_energy_comparison (Q r) (deriv Q r) (f r,g r)
    (deriv f r,deriv g r) c D (omega-1) hc hm hdQ (by linarith)).2
  rw [hv,hd] at hb
  have he : 1+(omega-1)=omega := by ring
  rw [he] at hb
  dsimp only [spectralWeightedCauchyEnergy,spectralCoordinateEnergy] at hb ⊢
  nlinarith only [hb]

end DefocusingNLS

end OAI
