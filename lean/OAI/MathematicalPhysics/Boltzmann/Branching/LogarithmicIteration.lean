import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! # Logarithmic time mass and vanishing finite-iteration remainders -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.PositiveIteration

theorem time_mass {a t C : ℝ} (ha : 0 < a) (hat : a ≤ t) (hC : 0 ≤ C) :
    (∫⁻ s in Ioc a t, ENNReal.ofReal (C/s)) = ENNReal.ofReal (C*Real.log (t/a)) := by
  have hi : IntervalIntegrable (fun s : ℝ => C/s) volume a t := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div continuousOn_id
    intro s hs
    rw [uIcc_of_le hat] at hs
    exact ne_of_gt (ha.trans_le hs.1)
  have hn : ∀ᵐ s ∂volume.restrict (Ioc a t), 0 ≤ C/s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact div_nonneg hC (ha.le.trans hs.1.le)
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hat).mp hi) hn,
    ← intervalIntegral.integral_of_le hat]
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_const_mul,integral_inv_of_pos ha (ha.trans_le hat)]
  rfl

theorem log_power_remainder_tendsto (C : ℝ) (j : ℕ) :
    Tendsto (fun a : ℝ => a*(C*Real.log (1/a))^j) (𝓝[>] 0) (𝓝 0) := by
  have h := (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (j : ℝ)
    (by norm_num : (-1 : ℝ) < 0)).tendsto_div_nhds_zero
  simp only [Real.rpow_natCast,Real.rpow_neg_one,div_inv_eq_mul] at h
  have hh := h.const_mul (C^j)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [Icc_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with a ha
  rw [one_div,Real.log_inv,abs_of_nonpos (Real.log_nonpos ha.1 ha.2),mul_pow]
  ring

theorem finite_remainder_tendsto (C : ℝ) (m : ℕ) :
    Tendsto (fun a : ℝ => a*∑ j ∈ Finset.range m, (C*Real.log (1/a))^j)
      (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_finsetSum (Finset.range m)
    (fun j _ => log_power_remainder_tendsto C j)
  simpa only [Finset.sum_const_zero,Finset.mul_sum] using h

end BoltzmannNonuniqueness.PositiveIteration

end

end OAI
