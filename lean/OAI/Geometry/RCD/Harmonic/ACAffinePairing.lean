import OAI.Geometry.RCD.Heat.ACDerivativeL2Endpoint

namespace OAI

/-! # Pairing a bounded affine residual with a varying coefficient -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates

theorem ac_zero_endpoint_pairing_bound {b z : ℝ → ℝ} {η : ℝ}
    (hb : AbsolutelyContinuousOnInterval b 0 1)
    (hz : AbsolutelyContinuousOnInterval z 0 1)
    (hz0 : z 0=0) (hz1 : z 1=0)
    (hbound : ∀ t∈Icc (0:ℝ) 1, |z t|≤η) :
    |∫ t in Icc (0:ℝ) 1, b t*deriv z t| ≤
      η*(∫ t in Icc (0:ℝ) 1, |deriv b t|) := by
  have he := hb.integral_mul_deriv_eq_deriv_mul hz
  simp only [hz0,hz1,mul_zero,sub_zero,zero_sub] at he
  have hei : (∫ t in Icc (0:ℝ) 1, b t*deriv z t)=
      -(∫ t in Icc (0:ℝ) 1, deriv b t*z t) := by
    simpa only [intervalIntegral.integral_of_le zero_le_one,integral_Icc_eq_integral_Ioc] using he
  have hi : IntegrableOn (fun t => η*|deriv b t|) (Icc (0:ℝ) 1) :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hb.intervalIntegrable_deriv).abs.const_mul η
  rw [hei,abs_neg]
  calc
    |∫ t in Icc (0:ℝ) 1, deriv b t*z t| ≤
        ∫ t in Icc (0:ℝ) 1, η*|deriv b t| := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [Real.norm_eq_abs,abs_mul,mul_comm η]
      exact mul_le_mul_of_nonneg_left (hbound t ht) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

end RegularPointCoordinates

end

end OAI
