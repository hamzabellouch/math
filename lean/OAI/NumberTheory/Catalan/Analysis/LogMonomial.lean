import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

open MeasureTheory Real Set Filter intervalIntegral
open scoped Topology Interval

namespace InternalCatalan

theorem intervalIntegrable_pow_neg_log (k : ℕ) :
    IntervalIntegrable (fun x : ℝ => x ^ k * (-Real.log x)) volume 0 1 := by
  exact intervalIntegrable_log'.neg.continuousOn_mul (continuous_pow k).continuousOn

theorem integral_pow_neg_log (k : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ k * (-Real.log x)) =
      1 / ((k + 1 : ℕ) : ℝ) ^ 2 := by
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hpow : Tendsto (fun x : ℝ => x ^ (k + 1)) (𝓝[>] 0) (𝓝 0) := by
    simpa using
      (tendsto_nhdsWithin_of_tendsto_nhds
        (Filter.tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0))).pow (k + 1)
  have hlog : Tendsto (fun x : ℝ => Real.log x * x ^ (k + 1))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      (tendsto_log_mul_rpow_nhdsGT_zero
        (show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) by positivity))
  have h := integral_eq_sub_of_hasDerivAt_of_tendsto
    (f := fun x : ℝ => x ^ (k + 1) / ((k + 1 : ℕ) : ℝ) ^ 2 -
      Real.log x * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ))
    (f' := fun x : ℝ => x ^ k * (-Real.log x))
    (fa := 0) (fb := 1 / ((k + 1 : ℕ) : ℝ) ^ 2)
    (show (0 : ℝ) < 1 by norm_num)
    (by
      intro x hx
      convert ((hasDerivAt_pow (k + 1) x).div_const
        (((k + 1 : ℕ) : ℝ) ^ 2)).sub
        (((Real.hasDerivAt_log hx.1.ne').mul
          (hasDerivAt_pow (k + 1) x)).div_const ((k + 1 : ℕ) : ℝ)) using 1
      simp only [Nat.add_sub_cancel, pow_succ]
      field_simp [hx.1.ne', hk]
      ring)
    (intervalIntegrable_pow_neg_log k)
    (by
      simpa using ((hpow.div_const (((k + 1 : ℕ) : ℝ) ^ 2)).sub
        (hlog.div_const ((k + 1 : ℕ) : ℝ))))
    (by
      have hc : ContinuousAt (fun x : ℝ =>
          x ^ (k + 1) / ((k + 1 : ℕ) : ℝ) ^ 2 -
          Real.log x * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) 1 := by
        fun_prop (disch := positivity)
      simpa using tendsto_nhdsWithin_of_tendsto_nhds hc.tendsto)
  simpa using h

end InternalCatalan

end OAI
