import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelCoefficientBudgetGrowth
import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelCoefficientParameters

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

private theorem kernel_budget_pow_exp {x : ℝ} (hx : 0 < x) (n : ℕ) :
    x^n = Real.exp ((n : ℝ)*Real.log x) := by
  rw [←Real.rpow_natCast, Real.rpow_def_of_pos hx]
  congr 1
  ring

theorem eventually_kernelCoefficient_budget (c δ ε : ℝ)
    (hc : 0 < c) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ (Z J J₀ : ℕ),
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      c*(Z : ℝ)/Real.log Z ≤ J → J ≤ 2*Z →
      commonCenterCutoff Z ≤ J₀ →
      let k := evenMomentParameter (parameterX T) Z
      commonCenterMomentScale J Z k/4 ≤ 2*(J : ℝ)*(J₀ : ℝ)^(k-1) →
      (2*(Z : ℝ))^k*((k.factorial : ℝ)/(J₀ : ℝ)^k)*(2/δ^k)^2 ≤
        (parameterX T : ℝ)^ε := by
  filter_upwards [eventually_kernelCoefficient_log_cost ε hε,
    eventually_kernel_population_inputs 1 (by norm_num),
    eventually_evenMomentParameter_bound,
    eventually_mul_rpow_le_rpow 14 (a := 3/5) (b := 1) (by norm_num),
    eventually_parameterX_log_bounds, eventually_ge_atTop (4/(c*δ^2))]
    with T hcost hpop hkbound hpow hX hTc
  intro Z J J₀ hZl hZu hJ hJu hJ₀
  dsimp only
  intro hcenter
  let k := evenMomentParameter (parameterX T) Z
  have hT : 0 < T := by linarith [hX.1]
  have hlogZ : 0 < Real.log Z := by linarith [hX.1]
  have hZ1 : (1 : ℝ) < Z := (Real.log_pos_iff (Nat.cast_nonneg Z)).mp hlogZ
  have hZp : (0 : ℝ) < Z := by linarith
  have hJp : (0 : ℝ) < J := (div_pos (mul_pos hc hZp) hlogZ).trans_le hJ
  have hJ₀1 : (1 : ℝ) ≤ J₀ := by
    exact_mod_cast (hpop Z J₀ hZl hJ₀).2.2.1
  have hkT : (k : ℝ) ≤ T :=
    (hkbound Z hZl).trans (by simpa only [Real.rpow_one] using hpow)
  have hbase := kernelCoefficient_budget_base_le hJp hZp hX.1 hc hδ hlogZ hJ hZu hkT hTc
  have hb := kernelCoefficient_budget_le hJp hJ₀1 hZ1.le hδ
    (by exact_mod_cast hJu) hcenter
  have hXpos : (0 : ℝ) < parameterX T := by
    have hh := (Real.log_pos_iff (Nat.cast_nonneg (parameterX T))).mp
      (show 0 < Real.log (parameterX T : ℝ) by linarith [hX.2.1])
    linarith
  calc
    _ ≤ 64*(Z : ℝ)^2*(2*(Z : ℝ)*(k : ℝ)/((J : ℝ)*δ^2))^k := hb
    _ ≤ 64*(Z : ℝ)^2*(T^3)^k := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hbase k) (by positivity)
    _ = Real.exp (Real.log 64+2*Real.log Z+3*(k : ℝ)*Real.log T) := by
      rw [←pow_mul, kernel_budget_pow_exp hZp 2, kernel_budget_pow_exp hT (3*k),
        Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 64)]
      push_cast
      ring
    _ ≤ Real.exp (Real.log 64+4*T+3*T*Real.log T) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right hkT (Real.log_nonneg hX.1)
      nlinarith
    _ ≤ Real.exp (ε*Real.log (parameterX T : ℝ)) := Real.exp_le_exp.mpr hcost
    _ = _ := by rw [Real.rpow_def_of_pos hXpos]; congr 1; ring

end Ostmann.QuadraticCenter

end

end OAI
