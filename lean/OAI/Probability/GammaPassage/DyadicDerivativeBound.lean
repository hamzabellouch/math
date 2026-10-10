import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace OAI

namespace GammaFPP
open Filter Topology

theorem dyadic_derivative_bound (G : ℝ → ℝ) (a m K : ℝ) (hK : 0 ≤ K)
    (hzero : G 0 = 0) (hd : HasDerivAt G m 0)
    (hrec : ∀ n : ℕ, G (a*(1/2 : ℝ)^n) ≤
      2*G (a*(1/2 : ℝ)^(n+1)) + K*((1/2 : ℝ)^n)^2) :
    G a ≤ a*m+2*K := by
  have hi : ∀ n : ℕ, G a ≤ G (a*(1/2 : ℝ)^n)/(1/2 : ℝ)^n +
      2*K*(1-(1/2 : ℝ)^n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hn : 0 < (1/2 : ℝ)^n := pow_pos (by norm_num) n
      have hdiv := div_le_div_of_nonneg_right (hrec n) hn.le
      calc
        _ ≤ G (a*(1/2 : ℝ)^n)/(1/2 : ℝ)^n + 2*K*(1-(1/2 : ℝ)^n) := ih
        _ ≤ (2*G (a*(1/2 : ℝ)^(n+1))+K*((1/2 : ℝ)^n)^2)/(1/2 : ℝ)^n +
            2*K*(1-(1/2 : ℝ)^n) := add_le_add hdiv le_rfl
        _ = _ := by
          rw [pow_succ]
          field_simp
          ring
  by_cases ha : a = 0
  · subst a
    simp only [hzero, zero_mul, zero_add]
    positivity
  have hp : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hb : Tendsto (fun n : ℕ => a*(1/2 : ℝ)^n) atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using hp.const_mul a
    · exact .of_forall (fun n => by simp [ha])
  have hsl := (hd.tendsto_slope.comp hb).const_mul a
  have hmain : Tendsto (fun n : ℕ => G (a*(1/2 : ℝ)^n)/(1/2 : ℝ)^n)
      atTop (𝓝 (a*m)) := by
    convert hsl using 1
    funext n
    simp only [Function.comp_def, slope, sub_zero, hzero, smul_eq_mul, vsub_eq_sub, sub_zero]
    field_simp [ha]
  have hc : Tendsto (fun n : ℕ => 2*K*(1-(1/2 : ℝ)^n)) atTop (𝓝 (2*K)) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hp).const_mul (2*K)
  exact ge_of_tendsto (hmain.add hc) (.of_forall hi)

end GammaFPP

end OAI
