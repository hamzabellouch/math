import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplifiedLower
import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterCostBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter

theorem amplifier_log_gain : (1/50:ℝ) ≤ Real.log (49/48:ℝ) := by
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<49/48)
  norm_num at hh
  linarith

theorem amplified_moment_scalar_lower {c δ X : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hX : 0 < Real.log X) (K k : ℕ)
    (hcost : |Real.log c|+(k:ℝ)*|Real.log δ|+3*Real.log (Real.log X) ≤ (K:ℝ)/250) :
    Real.sqrt X*Real.exp ((2/125:ℝ)*K) ≤
      c*Real.sqrt X/(Real.log X)^3*(49/48:ℝ)^K*δ^k := by
  have hval : 0 < c*(49/48:ℝ)^K*δ^k/(Real.log X)^3 := by positivity
  have hlog : (2/125:ℝ)*K ≤ Real.log (c*(49/48:ℝ)^K*δ^k/(Real.log X)^3) := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (ne_of_gt hc) (by positivity),Real.log_pow,Real.log_pow,Real.log_pow]
    have hb := mul_le_mul_of_nonneg_left amplifier_log_gain (Nat.cast_nonneg K : (0:ℝ) ≤ K)
    have hd := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log δ)) (Nat.cast_nonneg k : (0:ℝ) ≤ k)
    have hcc := neg_abs_le (Real.log c)
    norm_num only [Nat.cast_ofNat] at *
    linarith
  have he : Real.exp ((2/125:ℝ)*K) ≤ c*(49/48:ℝ)^K*δ^k/(Real.log X)^3 := by
    calc
      _ ≤ Real.exp (Real.log (c*(49/48:ℝ)^K*δ^k/(Real.log X)^3)) := Real.exp_le_exp.mpr hlog
      _ = _ := Real.exp_log hval
  have hh := mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg X)
  convert hh using 1; ring

theorem eventually_amplified_moment_scalar_lower (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ Z z : ℕ,
      T/2 ≤ Real.log Z → Real.log Z ≤ 2*T →
      1 ≤ z → T^auxiliaryExponent/2 ≤ Real.log z →
      Real.log z ≤ 2*T^auxiliaryExponent →
      Real.sqrt (parameterX T:ℝ)*Real.exp ((2/125:ℝ)*auxiliaryK Z z) ≤
        c*Real.sqrt (parameterX T:ℝ)/(Real.log (parameterX T:ℝ))^3*
          (49/48:ℝ)^auxiliaryK Z z*δ^evenMomentParameter (parameterX T) Z := by
  let C : ℝ := |Real.log c|+|Real.log δ|+3
  have hC : 0 < C := by dsimp [C]; positivity
  filter_upwards [eventually_moment_log_cost_le C (1/250) hC (by norm_num),
    eventually_parameterX_log_bounds,
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp parameterX_tendsto)).eventually_ge_atTop 1]
    with T hcost hX hlogX
  intro Z z hZl hZu hz hzl hzu
  have hT : 0 < T := by linarith [hX.1]
  have hlogZ : 0 < Real.log Z := by linarith
  have hlogXp : 0 < Real.log (parameterX T:ℝ) := by linarith
  have hk := (evenMomentParameter_bounds (parameterX T) Z (by positivity)).1
  have hk1 : (1:ℝ) ≤ evenMomentParameter (parameterX T) Z := by
    have : 0 ≤ Real.log (parameterX T:ℝ)/Real.log Z := by positivity
    linarith
  have hloglog : 0 ≤ Real.log (Real.log (parameterX T:ℝ)) := Real.log_nonneg hlogX
  apply amplified_moment_scalar_lower hc hδ hlogXp
  have hh := hcost Z z hZl hZu hz hzl hzu
  have hcc := mul_le_mul_of_nonneg_left hk1 (abs_nonneg (Real.log c))
  have hrest : 3*Real.log (Real.log (parameterX T:ℝ)) ≤ C*Real.log (Real.log (parameterX T:ℝ)) := by
    apply mul_le_mul_of_nonneg_right _ hloglog
    dsimp [C]
    linarith [abs_nonneg (Real.log c),abs_nonneg (Real.log δ)]
  dsimp [C] at hh hrest
  nlinarith [abs_nonneg (Real.log δ),(Nat.cast_nonneg (evenMomentParameter (parameterX T) Z) : (0:ℝ) ≤ _)]

end Ostmann.QuadraticCenter

end

end OAI
