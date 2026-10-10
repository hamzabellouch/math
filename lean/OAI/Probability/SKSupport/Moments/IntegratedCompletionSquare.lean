import Mathlib
import OAI.Probability.SKSupport.Model

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto

lemma integrated_completion_square (a b c u : ℝ) (hab : a ≤ b) (hc : 0 ≤ c)
    {α : ℝ → ℝ} (hα : IntervalIntegrable α volume a b)
    (hα₂ : IntervalIntegrable (fun t => (α t)^2) volume a b) :
    u * (∫ t in a..b, c*α t) - (1/2:ℝ)*(∫ t in a..b, c*(α t)^2) ≤
      (b-a)*c/2*u^2 := by
  have hmono : (∫ t in a..b, u*(c*α t)-(1/2:ℝ)*(c*(α t)^2)) ≤
      ∫ _t in a..b, c/2*u^2 := by
    apply intervalIntegral.integral_mono_on hab
      ((hα.const_mul c).const_mul u |>.sub ((hα₂.const_mul c).const_mul (1/2:ℝ)))
      intervalIntegrable_const
    intro t ht
    nlinarith [mul_nonneg hc (sq_nonneg (α t-u))]
  rw [intervalIntegral.integral_sub ((hα.const_mul c).const_mul u)
    ((hα₂.const_mul c).const_mul (1/2:ℝ)), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hmono
  simpa only [intervalIntegral.integral_const_mul, smul_eq_mul, mul_div_assoc, mul_assoc] using hmono

lemma completion_square_feedback (c h u : ℝ) :
    u*(c*h*u)-(c*h/2*u^2) = h*c/2*u^2 := by ring

lemma finite_mesh_verification (F K : ℕ → ℝ) (n : ℕ) (ε : ℝ)
    (hstep : ∀ k < n, F (k+1)-F k-K k ≤ ε) :
    F n-F 0-(∑ k ∈ Finset.range n, K k) ≤ (n:ℝ)*ε := by
  have hh := Finset.sum_le_sum (s := Finset.range n)
    (f := fun k => F (k+1)-F k-K k) (g := fun _ => ε)
    (fun k hk => hstep k (Finset.mem_range.mp hk))
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub F] at hh
  simpa using hh

lemma vanishing_mesh_error (T A C : ℝ) :
    Tendsto (fun n : ℕ =>
      (n:ℝ) * (A*(T/(n:ℝ))*Real.sqrt (T/(n:ℝ)) + C*(T/(n:ℝ))^2)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun n : ℕ => T/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hn
  have hlim : Tendsto (fun n : ℕ => A*T*Real.sqrt (T/(n:ℝ)) + C*T*(T/(n:ℝ)))
      atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds.mul (Real.continuous_sqrt.tendsto 0 |>.comp hh)).add
      (tendsto_const_nhds.mul hh))
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0<1) hn))
  field_simp

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
