import OAI.Probability.InvariantIsing.Gaussian.MPDensitySubstitution

namespace OAI

/-! Integrability and exact mass of the literal MP density, including the critical aspect ratio. -/
noncomputable section
open Real Set MeasureTheory
namespace InvariantIsing

lemma mpDensity_nonneg {α x : ℝ} (hx : x ∈ Icc (marchenkoPasturA α) (marchenkoPasturB α)) :
    0 ≤ mpDensity α x := by
  have hA : 0 ≤ marchenkoPasturA α := sq_nonneg _
  have hx0 := hA.trans hx.1
  exact div_nonneg (sqrt_nonneg _) (by positivity)

lemma mpDensity_integrable {α : ℝ} (hα : 0 < α) :
    IntegrableOn (mpDensity α) (Icc (marchenkoPasturA α) (marchenkoPasturB α)) := by
  have hi : IntegrableOn (fun x => (2*α/Real.pi)*((sin x)^2/mpAngle α x)) (Icc 0 Real.pi) := by
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le pi_pos.le).mp
      (mp_angular_sine_integrable hα)).const_mul (2*α/Real.pi)
  have hc : IntegrableOn (fun x => (-(2*sqrt α)*sin x) • mpDensity α (mpAngle α x)) (Icc 0 Real.pi) := by
    apply hi.neg.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simp only [Pi.neg_apply,smul_eq_mul]
    calc
      _ = -((2*sqrt α*sin x)*mpDensity α (mpAngle α x)) := by rw [mpAngle_density_jacobian hα.le hx]
      _ = _ := by ring
  have he := (integrableOn_Icc_deriv_smul_iff_of_deriv_nonpos
    (f := mpAngle α) (f' := fun x => -(2*sqrt α)*sin x) (g := mpDensity α)
    (continuous_mpAngle α).continuousOn (fun x _ => mpAngle_hasDerivAt α x)
    (fun _ hx => mpAngle_deriv_nonpos hx) pi_pos.le).mp hc
  simpa only [(mpAngle_endpoints hα.le).1,(mpAngle_endpoints hα.le).2] using he

theorem mpDensity_integral {α : ℝ} (hα : 0 < α) :
    (∫ x in Icc (marchenkoPasturA α) (marchenkoPasturB α), mpDensity α x) = min 1 α := by
  have h := mpDensity_substitution hα (fun _ => 1)
  simp only [mul_one] at h
  rw [h,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le pi_pos.le,
    intervalIntegral.integral_const_mul]
  exact mp_angular_continuous_mass hα

end InvariantIsing

end

end OAI
