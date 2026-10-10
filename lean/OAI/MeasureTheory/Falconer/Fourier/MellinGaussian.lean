import OAI.MeasureTheory.Falconer.Fourier.GaussianRepresentation
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem lintegral_Ioi_inv (g : ℝ → ℝ≥0∞) :
    (∫⁻ t : ℝ in Ioi 0, g t) =
      ∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal ((a^2)⁻¹) * g a⁻¹ := by
  have him : (fun a : ℝ => a⁻¹) '' Ioi 0 = Ioi 0 := by
    ext t
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact (inv_pos.mpr (show 0 < a from ha) : 0 < a⁻¹)
    · intro ht
      exact ⟨t⁻¹, (show 0 < t⁻¹ from inv_pos.mpr ht), inv_inv t⟩
  have h := lintegral_image_eq_lintegral_abs_deriv_mul
    (f := fun a : ℝ => a⁻¹) (f' := fun a => -(a^2)⁻¹)
    measurableSet_Ioi
    (fun a ha => (hasDerivAt_inv (ne_of_gt ha)).hasDerivWithinAt)
    (fun a _ b _ hab => inv_injective hab) g
  rw [him] at h
  simpa only [abs_neg, abs_inv, abs_pow, sq_abs] using h

theorem inverse_mellin_power {a : ℝ} (ha : 0 < a) (v : ℝ) :
    (a^2)⁻¹ * (a⁻¹)^(v-1) = a^(-v-1) := by
  rw [Real.inv_rpow ha.le, ← Real.rpow_neg ha.le,
    ← Real.rpow_two, ← Real.rpow_neg ha.le, ← Real.rpow_add ha]
  congr 1
  ring

theorem inverse_gaussian_mellin {v k : ℝ} (hv : 0 < v) (hk : 0 < k) :
    (∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal (a^(-v-1)*Real.exp (-k/a))) =
      ENNReal.ofReal ((1/k)^v * Real.Gamma v) := by
  have hi : IntegrableOn (fun t : ℝ => t^(v-1)*Real.exp (-(k*t))) (Ioi 0) := by
    by_contra hn
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hv hk
    rw [integral_undef hn] at h
    exact (mul_pos (Real.rpow_pos_of_pos (one_div_pos.mpr hk) v) (Real.Gamma_pos_of_pos hv)).ne' h.symm
  have hnon : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ => t^(v-1)*Real.exp (-(k*t))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
  rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi hv hk,
    ofReal_integral_eq_lintegral_ofReal hi hnon]
  conv_rhs => rw [lintegral_Ioi_inv]
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with a ha
  rw [← ENNReal.ofReal_mul (by positivity), ← mul_assoc, inverse_mellin_power ha]
  congr 1
  congr 1
  ring_nf

theorem lintegral_Ioi_power_eq_top (v : ℝ) :
    (∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal (a^v)) = ∞ := by
  by_contra hn
  have hnon : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun a : ℝ => a^v) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with a ha
    exact Real.rpow_nonneg ha.le _
  have hi := (lintegral_ofReal_ne_top_iff_integrable (by fun_prop) hnon).mp hn
  exact not_integrableOn_Ioi_rpow v hi

theorem source_kernel_gaussian_mixture_all {d u : ℝ} (hd : 0 ≤ d) (hu : 0 < u) :
    (ENNReal.ofReal d)^(-u) =
      ENNReal.ofReal (Real.pi^(u/2)/Real.Gamma (u/2)) *
        ∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal (a^(u/2-1)) *
          ENNReal.ofReal (Real.exp (-(Real.pi*a*d^2))) := by
  rcases eq_or_lt_of_le hd with hzero | hpos
  · subst d
    simp only [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (neg_neg_of_pos hu),
      zero_pow (by norm_num : 2 ≠ 0), mul_zero, neg_zero, Real.exp_zero,
      ENNReal.ofReal_one, mul_one, lintegral_Ioi_power_eq_top]
    have hc : 0 < ENNReal.ofReal (Real.pi^(u/2)/Real.Gamma (u/2)) := by
      apply ENNReal.ofReal_pos.mpr
      exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by linarith))
    exact (ENNReal.mul_top hc.ne').symm
  · have hi := gaussian_mixture_integrable hpos hu Real.pi_pos
    have hnon : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun a : ℝ => a^(u/2-1)*Real.exp (-(Real.pi*a*d^2))) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with a ha
      exact mul_nonneg (Real.rpow_nonneg ha.le _) (Real.exp_pos _).le
    rw [ENNReal.ofReal_rpow_of_pos hpos,
      source_inverse_power_gaussian_integral hpos hu, ENNReal.ofReal_mul (by positivity),
      ofReal_integral_eq_lintegral_ofReal hi hnon]
    congr 1
    apply lintegral_congr
    intro a
    exact ENNReal.ofReal_mul' (Real.exp_pos _).le

theorem source_mellin_coefficient {d : ℝ} (hd : 0 < d) (n u : ℝ) :
    (1/(Real.pi*d^2))^((n-u)/2) * Real.Gamma ((n-u)/2) =
      ((1/Real.pi)^((n-u)/2) * Real.Gamma ((n-u)/2)) * d^(u-n) := by
  have hp : (d^2)^((n-u)/2) = d^(n-u) := by
    rw [← Real.rpow_natCast_mul hd.le]
    congr 1
    ring
  rw [show 1/(Real.pi*d^2) = (1/Real.pi)*(d^2)⁻¹ by ring,
    Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity), hp,
    ← Real.rpow_neg hd.le]
  rw [show -(n-u) = u-n by ring]
  ring

theorem source_weight_gaussian_mixture {d : ℝ} (hd : 0 < d) {n u : ℝ} (hun : u < n) :
    (∫⁻ a : ℝ in Ioi 0, ENNReal.ofReal (a^(u/2-1)) *
      ENNReal.ofReal (a^(-n/2)) * ENNReal.ofReal (Real.exp (-Real.pi*d^2/a))) =
      ENNReal.ofReal ((1/Real.pi)^((n-u)/2) * Real.Gamma ((n-u)/2)) *
        ENNReal.ofReal (d^(u-n)) := by
  have h := inverse_gaussian_mellin (v := (n-u)/2) (k := Real.pi*d^2)
    (by linarith) (by positivity)
  rw [source_mellin_coefficient hd n u, ENNReal.ofReal_mul (by positivity)] at h
  rw [← h]
  apply lintegral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with a ha
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _), ← Real.rpow_add ha,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _)]
  congr 2
  · congr 1
    ring
  · congr 1
    ring

end PlanarFalconer

end OAI
