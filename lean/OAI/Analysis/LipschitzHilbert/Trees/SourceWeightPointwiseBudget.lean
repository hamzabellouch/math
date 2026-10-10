import OAI.Analysis.LipschitzHilbert.Estimates.TopWeight
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Elementary pointwise consequences of the actual top weights and the
polynomial count cutoff. They supply the uniform weight and logarithmic
mass bounds used in central interpolation and boundary averaging. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert

theorem SlopeBox.weight_le_two_rpow (T : SlopeBox) {K D : ℝ}
    (hK : 0 < K) (hD : 0 ≤ D) (z : ℝ×ℝ) : T.weight K D z ≤ (2:ℝ)^D := by
  unfold weight
  have hb : 1 ≤ 1+T.radius z/K := le_add_of_nonneg_right
    (div_nonneg (T.radius_nonnegative z) hK.le)
  exact mul_le_of_le_one_right (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_le_one_of_one_le_of_nonpos hb (neg_nonpos.mpr hD))

theorem SlopeBox.weight_mono_dilation (T : SlopeBox) {K K' D : ℝ}
    (hK : 0 < K) (hKK : K ≤ K') (hD : 0 ≤ D) (z : ℝ×ℝ) :
    T.weight K D z ≤ T.weight K' D z := by
  have hK' : 0 < K' := hK.trans_le hKK
  have hr := T.radius_nonnegative z
  have hb : 0 < 1+T.radius z/K' := by positivity
  unfold weight
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
  apply Real.rpow_le_rpow_of_nonpos hb _ (neg_nonpos.mpr hD)
  linarith [div_le_div_of_nonneg_left (T.radius_nonnegative z) hK hKK]

theorem eventually_count_log_bound (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ n N : ℝ, n ≤ L^C*N → 0 < N → Real.log N ≤ L →
      Real.log (max 1 n) ≤ 2*L := by
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero C 1 (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),
    ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with L hL hsmall
  intro n N hn hN hlog
  have hNexp : N ≤ Real.exp L := (Real.log_le_iff_le_exp hN).mp hlog
  have hpoly : L^C ≤ Real.exp L := by
    have h := mul_le_mul_of_nonneg_right hsmall.le (Real.exp_pos L).le
    simpa only [one_mul,neg_mul,one_mul,mul_assoc,← Real.exp_add,neg_add_cancel,
      Real.exp_zero,mul_one] using h
  have hexp : L^C*N ≤ Real.exp (2*L) := by
    calc
      _ ≤ Real.exp L*Real.exp L := mul_le_mul hpoly hNexp hN.le (Real.exp_pos _).le
      _ = _ := by rw [←Real.exp_add]; congr 1; ring
  have hmax : max 1 n ≤ Real.exp (2*L) := max_le
    (Real.one_le_exp (by linarith)) (hn.trans hexp)
  exact (Real.log_le_iff_le_exp (lt_of_lt_of_le zero_lt_one (le_max_left 1 n))).mpr hmax

end LipschitzHilbert

end

end OAI
