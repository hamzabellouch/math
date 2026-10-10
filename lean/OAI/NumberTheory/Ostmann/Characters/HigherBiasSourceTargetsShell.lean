import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Characters.HigherBiasSourceTargets
open Filter
open scoped Topology

theorem eventually_source_shell_reserves :
    ∀ᶠ k : ℕ in atTop,
      Real.log 10 ≤ (Real.log 2-2*(1/10000:ℝ))*(k:ℝ) ∧
      Real.log 600 ≤ (5-Real.log 4-(1/10000:ℝ))*(k:ℝ) ∧
      Real.exp (-((1/10000:ℝ)*k)) < 1/4 := by
  have hlog2lo := Real.log_two_gt_d9
  have hlog2hi := Real.log_two_lt_d9
  have hlog4 : Real.log 4=2*Real.log 2 := by
    rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.log_pow]
    norm_num
  have hpos1 : 0 < Real.log 2-2*(1/10000:ℝ) := by linarith
  have hpos2 : 0 < 5-Real.log 4-(1/10000:ℝ) := by rw [hlog4]; linarith
  have hnat : Tendsto (fun k:ℕ => (k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [(hnat.const_mul_atTop hpos1).eventually_ge_atTop (Real.log 10),
    (hnat.const_mul_atTop hpos2).eventually_ge_atTop (Real.log 600),
    (hnat.const_mul_atTop (by norm_num : (0:ℝ)<1/10000)).eventually_ge_atTop (Real.log 8)]
    with k h1 h2 h3
  refine ⟨h1,h2,?_⟩
  calc
    _ ≤ Real.exp (-Real.log 8) := Real.exp_le_exp.mpr (by linarith)
    _ = 1/8 := by rw [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<8)]; norm_num
    _ < _ := by norm_num

theorem eventually_source_target_shell_location :
    ∀ᶠ k : ℕ in atTop, ∀ U u T logX : ℝ,
      U ≤ u → u ≤ U+2*(1/10000:ℝ)*k →
      (1/10:ℝ)*(2:ℝ)^k*Real.exp u ≤ T →
      T ≤ 600*(4:ℝ)^k*Real.exp u →
      999*(4:ℝ)^k*Real.exp u ≤ logX →
      U ≤ Real.log T-2*(1/10000:ℝ)*k ∧
      Real.log T-(1/10000:ℝ)*k ≤ U+5*k ∧
      T*Real.exp (-((1/10000:ℝ)*k)) < logX/4 := by
  filter_upwards [eventually_source_shell_reserves] with k hk
  intro U u T logX hU hu hTlo hThi hX
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hTlo
  have hlo := Real.log_le_log (by positivity : (0:ℝ)<(1/10:ℝ)*(2:ℝ)^k*Real.exp u) hTlo
  have hhi := Real.log_le_log hTpos hThi
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_mul (by norm_num) (by positivity),Real.log_pow,Real.log_exp] at hlo
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_mul (by norm_num) (by positivity),Real.log_pow,Real.log_exp] at hhi
  have hlogtenth : Real.log (1/10:ℝ) = -Real.log 10 := by
    rw [one_div,Real.log_inv]
  rw [hlogtenth] at hlo
  refine ⟨by nlinarith [hk.1],by nlinarith [hk.2.1],?_⟩
  have hp : 0 < (4:ℝ)^k*Real.exp u := by positivity
  have hm := mul_le_mul_of_nonneg_right hThi (Real.exp_pos (-((1/10000:ℝ)*k))).le
  have hs := mul_lt_mul_of_pos_left hk.2.2 (by positivity : (0:ℝ)<600*((4:ℝ)^k*Real.exp u))
  nlinarith [hm,hs]

theorem eventually_source_target_shell_interval :
    ∀ᶠ k : ℕ in atTop, ∀ U u T logX : ℝ,
      U ≤ u → u ≤ U+2*(1/10000:ℝ)*k →
      (1/10:ℝ)*(2:ℝ)^k*Real.exp u ≤ T →
      T ≤ 600*(4:ℝ)^k*Real.exp u →
      999*(4:ℝ)^k*Real.exp u ≤ logX →
      Set.Icc (Real.log T-2*(1/10000:ℝ)*k) (Real.log T-(1/10000:ℝ)*k) ⊆
        Set.Icc U (U+5*k) ∧
      T*Real.exp (-((1/10000:ℝ)*k)) < logX/4 := by
  filter_upwards [eventually_source_target_shell_location] with k hk
  intro U u T logX hU hu hTlo hThi hX
  obtain ⟨hlo,hhi,hcut⟩ := hk U u T logX hU hu hTlo hThi hX
  refine ⟨?_,hcut⟩
  intro x hx
  exact ⟨hlo.trans hx.1,hx.2.trans hhi⟩

end Ostmann.Characters.HigherBiasSourceTargets

end

end OAI
