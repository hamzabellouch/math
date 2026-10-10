import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

namespace OAI

/-! # Endpoint control from an almost-everywhere interior derivative bound -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates

theorem ac_endpoint_bound {f : ℝ → ℝ} {L : ℝ}
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (h : ∀ᵐ t : ℝ, t∈Ioo (0:ℝ) 1 → |deriv f t|≤L) :
    |f 1-f 0|≤L := by
  have hi : ∀ᵐ t ∂volume.restrict (Ioo (0:ℝ) 1), |deriv f t|≤L := by
    filter_upwards [ae_restrict_of_ae h,ae_restrict_mem measurableSet_Ioo] with t ht hs
    exact ht hs
  have hc : ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1), |deriv f t|≤L := by
    rwa [← restrict_Ioo_eq_restrict_Icc]
  have hb : ∀ᵐ t : ℝ, t∈uIoc (0:ℝ) 1 → ‖deriv f t‖≤L := by
    rw [uIoc_of_le zero_le_one]
    exact (ae_restrict_iff' measurableSet_Ioc).mp
      (ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hc)
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const_ae hb
  rw [hf.integral_deriv_eq_sub] at hh
  simpa only [Real.norm_eq_abs,sub_zero,abs_one,mul_one] using hh

end RegularPointCoordinates

end

end OAI
