import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixDTendstoTop

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def codegreeNoiseRadius (n : ℕ) : ℝ := (n : ℝ)^(-1/10000 : ℝ)
noncomputable def codegreeNoiseDenominator (n : ℕ) : ℝ :=
  4*((6/prefixD n)*(4+8*Real.log n+codegreeNoiseRadius n+6/prefixD n)+
    (6/prefixD n)*codegreeNoiseRadius n)

theorem codegree_noise_exponent_lower : ∀ᶠ n : ℕ in atTop,
    (n : ℝ)^(1/2500 : ℝ) ≤ codegreeNoiseRadius n^2/codegreeNoiseDenominator n := by
  have hlog := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2500)).comp_tendsto
    tendsto_natCast_atTop_atTop).bound (by norm_num : (0 : ℝ) < 1/384)
  have hpow : Tendsto (fun n : ℕ => (n : ℝ)^(1/2500 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2500)).comp tendsto_natCast_atTop_atTop
  filter_upwards [prefixD_eventual_envelope,prefixD_tendsto_atTop.eventually_ge_atTop 6,
    hlog,hpow.eventually_ge_atTop 336,eventually_ge_atTop (1 : ℕ)] with n hD hD6 hl hn336 hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hD0 : 0 < prefixD n := by linarith
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hc0 : 0 < 6/prefixD n := by positivity
  have hc1 : 6/prefixD n ≤ 1 := (div_le_one hD0).mpr hD6
  have hr0 : 0 < codegreeNoiseRadius n := Real.rpow_pos_of_pos hn0 _
  have hr1 : codegreeNoiseRadius n ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hc : 6/prefixD n ≤ 6*(n : ℝ)^(-1/1000 : ℝ) := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 6)
      (Real.rpow_pos_of_pos hn0 (1/1000 : ℝ)) hD.1
    calc
      _ ≤ 6/(n : ℝ)^(1/1000 : ℝ) := hh
      _ = _ := by
        rw [show (-1/1000 : ℝ) = -(1/1000 : ℝ) by norm_num,Real.rpow_neg hn0.le]
        rfl
  have hr2 : codegreeNoiseRadius n^2 = (n : ℝ)^(-1/5000 : ℝ) := by
    unfold codegreeNoiseRadius
    rw [← Real.rpow_natCast,← Real.rpow_mul hn0.le]
    norm_num
  have hd0 : 0 < codegreeNoiseDenominator n := by unfold codegreeNoiseDenominator; positivity
  have hd : codegreeNoiseDenominator n ≤ (n : ℝ)^(-1/1000 : ℝ)*(24*(7+8*Real.log n)) := by
    unfold codegreeNoiseDenominator
    calc
      _ = 4*(6/prefixD n)*(4+8*Real.log n+codegreeNoiseRadius n+6/prefixD n+codegreeNoiseRadius n) := by ring
      _ ≤ 4*(6/prefixD n)*(7+8*Real.log n) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith only [hr1,hc1]
      _ ≤ 4*(6*(n : ℝ)^(-1/1000 : ℝ))*(7+8*Real.log n) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num))
          (by positivity)
      _ = _ := by ring
  have hsmall : 24*(7+8*Real.log (n : ℝ)) ≤ (n : ℝ)^(1/2500 : ℝ) := by
    dsimp at hl
    rw [abs_of_nonneg hln,abs_of_nonneg (Real.rpow_nonneg hn0.le (1/2500 : ℝ))] at hl
    linarith only [hl,hn336]
  have hd' := hd.trans (mul_le_mul_of_nonneg_left hsmall
    (Real.rpow_nonneg hn0.le (-1/1000 : ℝ)))
  apply (le_div_iff₀ hd0).mpr
  have hh := mul_le_mul_of_nonneg_left hd' (Real.rpow_nonneg hn0.le (1/2500 : ℝ))
  rw [← Real.rpow_add hn0,← Real.rpow_add hn0] at hh
  rw [hr2]
  convert hh using 1; norm_num

end SharpTerminalLeave

end

end OAI
