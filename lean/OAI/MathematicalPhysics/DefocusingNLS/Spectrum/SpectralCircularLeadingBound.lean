import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularUniqueness

namespace OAI

/-! The leading circular field is bounded on each finite radial interval. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem circularLeadingField_norm (t : ℝ) (z : E₄) :
    ‖circularLeadingField t z‖ ≤ (Real.exp (2*t)/2)*‖z‖ := by
  have hc : 0 ≤ Real.exp (2*t)/2 := by positivity
  have hp : ‖z.1.2‖ ≤ ‖z‖ := (norm_snd_le z.1).trans (norm_fst_le z)
  have hm : ‖z.2.2‖ ≤ ‖z‖ := (norm_snd_le z.2).trans (norm_snd_le z)
  have he : ‖(Real.exp (2*t)/2 : ℝ)‖ = Real.exp (2*t)/2 := Real.norm_of_nonneg hc
  change max (max ‖(0 : ℂ)‖ ‖-Complex.I*(Real.exp (2*t)/2 : ℝ)*z.1.2‖)
    (max ‖(0 : ℂ)‖ ‖Complex.I*(Real.exp (2*t)/2 : ℝ)*z.2.2‖) ≤ _
  simp only [norm_zero,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_real,he]
  exact max_le (max_le (mul_nonneg hc (norm_nonneg z)) (mul_le_mul_of_nonneg_left hp hc))
    (max_le (mul_nonneg hc (norm_nonneg z)) (mul_le_mul_of_nonneg_left hm hc))

end DefocusingNLS

end OAI
