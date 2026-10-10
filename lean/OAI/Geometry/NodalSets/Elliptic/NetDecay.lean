import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace Yau.Probability
open Filter
open scoped Topology

lemma net_small_ball_rate (C c n : ℝ) (hc : 0 < c) (hn : 0 < n) :
    C*n^276*(12*(Real.sqrt (c/n))⁻¹*(2/n^56)/Real.sqrt (2*Real.pi))^5 =
      (C*(24/(Real.sqrt c*Real.sqrt (2*Real.pi)))^5)/(n*Real.sqrt n) := by
  have hs := Real.sq_sqrt hn.le
  have hs0 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have hc0 : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have hp0 : Real.sqrt (2*Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [Real.sqrt_div hc.le,inv_div]
  field_simp
  have hs6 : (Real.sqrt n)^6 = n^3 := by
    calc
      _ = ((Real.sqrt n)^2)^3 := by ring
      _ = n^3 := by rw [hs]
  ring_nf
  rw [hs6]

lemma tendsto_net_rate (C : ℝ) :
    Tendsto (fun n : ℕ ↦ C/((n:ℝ)*Real.sqrt n)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ ↦ Real.sqrt (n:ℝ)) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow,Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).comp tendsto_natCast_atTop_atTop
  have h := (tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ hs).inv_tendsto_atTop
  simpa only [div_eq_mul_inv,mul_zero,Pi.inv_apply] using h.const_mul C

lemma tendsto_coefficient_tail_rate (C : ℝ) :
    Tendsto (fun n : ℕ ↦ C*(n:ℝ)^2*Real.exp (-(n:ℝ)^2/8)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ ↦ (n:ℝ)^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/8) (by norm_num)).comp hpow
  simpa only [Function.comp_def,Real.rpow_one,mul_zero,mul_assoc,show ∀ x : ℝ, -(1/8)*x = -x/8 by intro x; ring]
    using h.const_mul C

end Yau.Probability

end OAI
