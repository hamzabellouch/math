import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeBoundaryEnergy

namespace OAI

/-! The same physical Cauchy energy controls the boundary term when the
pressure-free equation is tested against its first component. -/

namespace DefocusingNLS

private theorem norm_pair_product (x y : ℂ) (E : ℝ)
    (hx : ‖x‖^2 ≤ E) (hy : ‖y‖^2 ≤ E) : ‖x‖*‖y‖ ≤ E := by
  nlinarith [sq_nonneg (‖x‖-‖y‖)]

theorem spectralGaugeSecondFlux_first_energy_bound (mu A : ℝ → ℝ) (f g : ℝ → ℂ)
    (r C : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C) (hm : 0 ≤ mu r) (hA : |A r| ≤ C*mu r) :
    ‖star (f r)*spectralGaugeSecondFlux mu A f g r‖ ≤
      r^11*(1+C)*mu r*(spectralCoordinateEnergy (f r,g r)+
        spectralCoordinateEnergy (deriv f r,deriv g r)) := by
  let E := spectralCoordinateEnergy (f r,g r)+spectralCoordinateEnergy (deriv f r,deriv g r)
  have hfe : ‖f r‖^2 ≤ E := by
    dsimp only [E,spectralCoordinateEnergy]
    nlinarith only [sq_nonneg ‖g r‖,sq_nonneg ‖deriv f r‖,sq_nonneg ‖deriv g r‖]
  have hdge : ‖deriv g r‖^2 ≤ E := by
    dsimp only [E,spectralCoordinateEnergy]
    nlinarith only [sq_nonneg ‖f r‖,sq_nonneg ‖g r‖,sq_nonneg ‖deriv f r‖]
  have hcross1 := norm_pair_product (f r) (deriv g r) E hfe hdge
  have hcross2 := norm_pair_product (f r) (f r) E hfe hfe
  have h := norm_add_le ((mu r : ℂ)*deriv g r) ((A r : ℂ)*f r)
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hm] at h
  have hb := mul_le_mul_of_nonneg_left h (norm_nonneg (f r))
  have ha := mul_le_mul_of_nonneg_left hA (mul_nonneg (norm_nonneg (f r)) (norm_nonneg (f r)))
  have h1 := mul_le_mul_of_nonneg_left hcross1 hm
  have h2 := mul_le_mul_of_nonneg_left hcross2 (mul_nonneg hC hm)
  have hsum : ‖f r‖*‖(mu r : ℂ)*deriv g r+(A r : ℂ)*f r‖ ≤ (1+C)*mu r*E := by
    nlinarith only [hb,ha,h1,h2]
  have hh := mul_le_mul_of_nonneg_left hsum (pow_nonneg hr 11)
  simpa only [spectralGaugeSecondFlux,norm_mul,norm_star,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hr,mul_assoc,mul_left_comm] using hh

theorem spectralGaugeSecondFlux_first_physical_energy_bound (mu A : ℝ → ℝ)
    (Q f g F G : ℝ → ℂ) (r C c D : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C) (hc : 0 < c)
    (hm : c ≤ ‖Q r‖^2) (hmass : mu r=‖Q r‖^2) (hA : |A r| ≤ C*mu r)
    (hQ : DifferentiableAt ℝ Q r) (hf : DifferentiableAt ℝ f r) (hg : DifferentiableAt ℝ g r)
    (hp : ∀ t, (Q t*(f t+Complex.I*g t),star (Q t)*(f t-Complex.I*g t))=(F t,G t))
    (hdQ : ‖deriv Q r‖ ≤ D) :
    ‖star (f r)*spectralGaugeSecondFlux mu A f g r‖ ≤
      (1+C)*(1+D^2/c)*spectralPhysicalShellDensity F G r := by
  have hb := spectralGaugeSecondFlux_first_energy_bound mu A f g r C hr hC
    (by rw [hmass]; positivity) hA
  have he := spectralRadialGaugeEnergy_pointwise 0 c D r hc le_rfl hr Q f g F G
    hQ hf hg hp hm hdQ
  simp only [spectralRadialEnergyDensity_eq,zero_mul,add_zero] at he
  have hs := mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ 1+C)
  rw [hmass] at hb
  dsimp only [spectralCoordinateEnergy,spectralPhysicalShellDensity] at hb hs ⊢
  nlinarith only [hb,hs]

end DefocusingNLS

end OAI
