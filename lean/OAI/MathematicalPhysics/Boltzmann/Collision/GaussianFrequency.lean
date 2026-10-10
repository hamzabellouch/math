import OAI.MathematicalPhysics.Boltzmann.Jets.JetProfiles
import OAI.MathematicalPhysics.Boltzmann.Branching.LossIntegrability

namespace OAI

/-! # The loss frequency of the normalized barrier Gaussian -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetGaussianMoments

namespace BoltzmannNonuniqueness.GaussianFrequency

def density (c b d : ℝ) (u : Velocity) (v : Velocity) : ℝ :=
  c * JetThermalLaw.scaled d u (kernel b) v

theorem density_eq_gaussian {d : ℝ} (hd : 0 < d) (c b : ℝ) (u v : Velocity) :
    density c b d u v = gaussian (c * (d ^ 3)⁻¹) (b / d ^ 2) u v := by
  simp only [density, JetThermalLaw.scaled, kernel, gaussian, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd), mul_pow]
  have he : -b * ((d⁻¹) ^ 2 * ‖v - u‖ ^ 2) = -(b / d ^ 2) * ‖v - u‖ ^ 2 := by
    field_simp
  rw [he]
  ring

theorem nonneg {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (b : ℝ) (u v : Velocity) :
    0 ≤ density c b d u v := by
  unfold density JetThermalLaw.scaled kernel
  positivity

theorem integrable {b d : ℝ} (hb : 0 < b) (hd : 0 < d) (c : ℝ) (u : Velocity) :
    Integrable (density c b d u) :=
  (JetThermalLaw.integrable_scaled (kernel_integrable hb) hd u).const_mul c

theorem centered_integrable {b d : ℝ} (hb : 0 < b) (hd : 0 < d) (c : ℝ) (u : Velocity) :
    Integrable (fun v => ‖v - u‖ * density c b d u v) := by
  convert (centered_scaled_integrable hb hd u).const_mul c using 1
  funext v
  unfold density
  ring

theorem mass_le {c b d : ℝ} (hc : 0 ≤ c) (hb : 1 ≤ b) (hd : 0 < d) (u : Velocity) :
    (∫ v, density c b d u v) ≤ c * mass := by
  simp only [density]
  rw [integral_const_mul, JetThermalLaw.integral_scaled _ hd u]
  exact mul_le_mul_of_nonneg_left (integral_kernel_le hb) hc

theorem centered_moment_le {c b d : ℝ} (hc : 0 ≤ c) (hb : 1 ≤ b) (hd : 0 < d)
    (u : Velocity) : (∫ v, ‖v - u‖ * density c b d u v) ≤ c * d * moment := by
  calc
    _ = c * (∫ v, ‖v - u‖ * JetThermalLaw.scaled d u (kernel b) v) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with v
      unfold density
      ring
    _ = c * d * (∫ v : Velocity, ‖v‖ * kernel b v) := by
      rw [integral_centered_scaled hd]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_moment_le hb) (mul_nonneg hc hd.le)

theorem first_moment_integrable {c b d : ℝ} (hc : 0 ≤ c) (hb : 0 < b) (hd : 0 < d)
    (u : Velocity) : Integrable (fun v => ‖v‖ * density c b d u v) := by
  apply ((integrable hb hd c u).const_mul ‖u‖ |>.add (centered_integrable hb hd c u)).mono'
    ((by fun_prop : AEStronglyMeasurable (fun v : Velocity => ‖v‖)).mul
      (integrable hb hd c u).aestronglyMeasurable)
  filter_upwards [] with v
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (nonneg hc hd.le b u v))]
  have hnorm : ‖v‖ ≤ ‖u‖ + ‖v - u‖ := by
    have := norm_add_le u (v - u)
    simpa only [add_sub_cancel, add_comm] using this
  simpa only [Pi.add_apply, add_mul] using mul_le_mul_of_nonneg_right hnorm (nonneg hc hd.le b u v)

theorem frequency_le {c b d : ℝ} (hc : 0 ≤ c) (hb : 1 ≤ b) (hd : 0 < d)
    (u v : Velocity) (x : Position) :
    frequency (fun p => density c b d u p.2) x v ≤
      2 * Real.pi * c * (mass * ‖v - u‖ + moment * d) := by
  have hbpos := lt_of_lt_of_le zero_lt_one hb
  have hi := integrable_frequency_integrand (fun p => density c b d u p.2) x v
    (integrable hbpos hd c u) (first_moment_integrable hc hbpos hd u)
  have hmaj := ((integrable hbpos hd c u).const_mul ‖v - u‖).add
    (centered_integrable hbpos hd c u)
  have hbound : (∫ w, ‖v - w‖ * density c b d u w) ≤
      ‖v - u‖ * (∫ w, density c b d u w) + ∫ w, ‖w - u‖ * density c b d u w := by
    calc
      _ ≤ ∫ w, ‖v - u‖ * density c b d u w + ‖w - u‖ * density c b d u w := by
        apply integral_mono hi hmaj
        intro w
        have hnorm : ‖v - w‖ ≤ ‖v - u‖ + ‖w - u‖ := by
          simpa only [sub_sub_sub_cancel_right, norm_sub_rev] using norm_sub_le (v - u) (w - u)
        simpa only [Pi.add_apply, add_mul] using mul_le_mul_of_nonneg_right hnorm (nonneg hc hd.le b u w)
      _ = _ := by rw [integral_add ((integrable hbpos hd c u).const_mul _) (centered_integrable hbpos hd c u), integral_const_mul]
  have hm := mul_le_mul_of_nonneg_left (mass_le hc hb hd u) (norm_nonneg (v - u))
  have hj := centered_moment_le hc hb hd u
  unfold frequency
  calc
    _ ≤ 2 * Real.pi * (‖v - u‖ * (c * mass) + c * d * moment) :=
      mul_le_mul_of_nonneg_left (hbound.trans (add_le_add hm hj)) (by positivity)
    _ = _ := by ring

end BoltzmannNonuniqueness.GaussianFrequency

end

end OAI
