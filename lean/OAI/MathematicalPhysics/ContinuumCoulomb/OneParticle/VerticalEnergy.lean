import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.VerticalMode

namespace OAI

/-! The normalized Gaussian actually attains transverse oscillator energy
`freq/2`, by the differential equation and integrable integration by parts. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def verticalForm (freq : ℝ) (u : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∫ z, deriv u z ^ 2) +
    (freq ^ 2 / 2) * (∫ z, z ^ 2 * u z ^ 2)

theorem verticalMode_second_product_integrable {freq : ℝ} (hfreq : 0 < freq) :
    Integrable (fun z => verticalMode freq z * deriv (deriv (verticalMode freq)) z) := by
  have h := ((verticalMode_moment_integrable hfreq 2).const_mul (freq ^ 2)).sub
    ((verticalMode_square_integrable hfreq).const_mul freq)
  convert h using 1
  funext z
  rw [verticalMode_second_deriv]
  simp only [Pi.sub_apply]
  ring

theorem verticalMode_energy_ibp {freq : ℝ} (hfreq : 0 < freq) :
    (∫ z, verticalMode freq z * deriv (deriv (verticalMode freq)) z) =
      -(∫ z, deriv (verticalMode freq) z ^ 2) := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := verticalMode freq) (g := deriv (verticalMode freq)) (v := (1 : ℝ))
    (by simpa only [fderiv_apply_one_eq_deriv, ← pow_two] using
      verticalMode_deriv_square_integrable hfreq)
    (by simpa only [fderiv_apply_one_eq_deriv] using verticalMode_second_product_integrable hfreq)
    ((verticalMode_memLp hfreq).integrable_mul (verticalMode_deriv_memLp hfreq))
    (fun z _ => (verticalMode_hasDerivAt freq z).differentiableAt)
    (fun z _ => (verticalMode_second_hasDerivAt freq z).differentiableAt)
  simpa only [fderiv_apply_one_eq_deriv, ← pow_two] using h

theorem verticalMode_energy {freq : ℝ} (hfreq : 0 < freq) :
    verticalForm freq (verticalMode freq) = freq / 2 := by
  have h := verticalMode_energy_ibp hfreq
  have heq : (∫ z, verticalMode freq z * deriv (deriv (verticalMode freq)) z) =
      freq ^ 2 * (∫ z, z ^ 2 * verticalMode freq z ^ 2) - freq := by
    simp_rw [verticalMode_second_deriv]
    rw [show (fun z => verticalMode freq z * ((freq ^ 2 * z ^ 2 - freq) * verticalMode freq z)) =
      (fun z => freq ^ 2 * (z ^ 2 * verticalMode freq z ^ 2) - freq * verticalMode freq z ^ 2)
      from by funext z; ring]
    rw [integral_sub ((verticalMode_moment_integrable hfreq 2).const_mul _)
      ((verticalMode_square_integrable hfreq).const_mul _), integral_const_mul,
      integral_const_mul, verticalMode_normalized hfreq, mul_one]
  unfold verticalForm
  linarith

end ContinuumCoulomb

end

end OAI
