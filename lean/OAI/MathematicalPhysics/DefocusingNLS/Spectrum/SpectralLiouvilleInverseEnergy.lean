import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalShellEnergy

namespace OAI

/-! The fixed-radius Liouville transformation also controls the physical
Cauchy energy from its transformed value and derivative. -/

namespace DefocusingNLS

private theorem inverse_scalar_energy (S u v : ℂ) (L : ℝ) (_hL : 0 ≤ L) (hS : ‖S‖ ≤ L) :
    ‖u‖^2+‖v‖^2 ≤ (3+2*L^2)*(‖u‖^2+‖v+S*u‖^2) := by
  have htri : ‖v‖ ≤ ‖v+S*u‖+L*‖u‖ := by
    have he : v=(v+S*u)-S*u := by ring
    calc
      ‖v‖ = ‖(v+S*u)-S*u‖ := congrArg norm he
      _ ≤ ‖v+S*u‖+‖S*u‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_mul]; gcongr
  have hs := pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hb : ‖v‖^2 ≤ 2*‖v+S*u‖^2+2*L^2*‖u‖^2 := by
    nlinarith [sq_nonneg (‖v+S*u‖-L*‖u‖)]
  nlinarith [mul_nonneg (sq_nonneg L) (sq_nonneg ‖v+S*u‖),sq_nonneg ‖u‖,sq_nonneg ‖v+S*u‖]

theorem spectralLiouvilleState_inverse_energy (h r : ℝ) (hh : |h| ≤ 1) (hr : 0 < r)
    (u v : ℂ) :
    r^11*(‖u‖^2+‖v‖^2) ≤ (3+2*(11/(2*r)+r/4)^2)*
      (‖homogeneousSpectralLocalizationFactor h r*u‖^2+
        ‖homogeneousSpectralLocalizationFactor h r*(v+homogeneousSpectralLocalizationSlope h r*u)‖^2) := by
  have hb := inverse_scalar_energy (homogeneousSpectralLocalizationSlope h r) u v
    (11/(2*r)+r/4) (by positivity) (spectralLiouvilleSlope_shell_bound h r r r hh hr le_rfl le_rfl)
  have he := mul_le_mul_of_nonneg_left hb (pow_nonneg hr.le 11)
  simp only [norm_mul,mul_pow,spectralLiouvilleFactor_norm_sq h r hr]
  nlinarith only [he]

theorem spectralPhysicalLiouvillePair_inverse_energy (r : ℝ) (hr : 0 < r) (f g : ℝ → ℂ) :
    spectralPhysicalShellDensity f g r ≤ (3+2*(11/(2*r)+r/4)^2)*
      (‖(spectralPhysicalLiouvillePair f g r).1.1‖^2+
        ‖(spectralPhysicalLiouvillePair f g r).1.2‖^2+
        ‖(spectralPhysicalLiouvillePair f g r).2.1‖^2+
        ‖(spectralPhysicalLiouvillePair f g r).2.2‖^2) := by
  have hp := spectralLiouvilleState_inverse_energy 1 r (by norm_num) hr (f r) (deriv f r)
  have hm := spectralLiouvilleState_inverse_energy (-1) r (by norm_num) hr (g r) (deriv g r)
  dsimp only [spectralPhysicalShellDensity,spectralPhysicalLiouvillePair,homogeneousSpectralLocalizationState]
  nlinarith only [hp,hm]

end DefocusingNLS

end OAI
