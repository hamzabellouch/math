import OAI.NumberTheory.Ostmann.Construction.SourceRangeSeparationScales

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction.RepeatedPriorBounds
open Filter

theorem cell_count_cost {k : ℕ} (hk : 0<k) {L : ℝ} (hL : 4≤L) :
    ((4*k+8:ℕ):ℝ)*L≤24*(Conclusion.bulkSize k L:ℝ) := by
  have hk1 : (1:ℝ)≤k := by exact_mod_cast hk
  have hpow : (k:ℝ)≤(k:ℝ)^4 := by
    simpa using pow_le_pow_right₀ hk1 (show 1≤4 by omega)
  have hkpow : (1:ℝ)≤(k:ℝ)^4 := hk1.trans hpow
  have hmul := mul_le_mul_of_nonneg_right hpow (show 0≤L by linarith)
  have hmul1 := mul_le_mul_of_nonneg_right hkpow (show 0≤L by linarith)
  have hm := (Conclusion.bulkSize_bounds k (show 0≤L by linarith)).1
  simp only [Conclusion.bulkScale] at hm
  push_cast
  nlinarith

theorem cell_center_ranges_eventually {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, 4≤L ∧
      favorableBlockWidth L/100≤Real.exp ((1/20:ℝ)*L)-2 ∧
      Real.exp ((9/10:ℝ)*L)+2≤Real.exp L/2 ∧
      2*(2:ℝ)^k*favorableBlockWidth L≤Real.exp L/2 ∧
      1≤Real.exp L/2 ∧ ((4*k+8:ℕ):ℝ)*L≤24*(Conclusion.bulkSize k L:ℝ) := by
  have hg := (exp_mul_tendsto (by norm_num : (0:ℝ)<1-9/10)).eventually_ge_atTop 6
  have ha := (exp_mul_tendsto (by norm_num : (0:ℝ)<1-1/100)).eventually_ge_atTop (4*(2:ℝ)^k)
  filter_upwards [SourceRangeSeparation.broad_range_gaps_eventually k,hg,ha,
    eventually_ge_atTop (4:ℝ)] with L hb hg ha hL
  have hw : 0≤favorableBlockWidth L := by linarith [hb.2.1]
  have hp : (1:ℝ)≤2^k := one_le_pow₀ (by norm_num)
  have he : 1≤Real.exp ((9/10:ℝ)*L) := Real.one_le_exp (by linarith)
  have hgm := mul_le_mul_of_nonneg_right hg (Real.exp_pos ((9/10:ℝ)*L)).le
  rw [← Real.exp_add,show ((1:ℝ)-9/10)*L+(9/10)*L=L by ring] at hgm
  have ham := mul_le_mul_of_nonneg_right ha (Real.exp_pos ((1/100:ℝ)*L)).le
  rw [← Real.exp_add,show ((1:ℝ)-1/100)*L+(1/100)*L=L by ring] at ham
  change (4*(2:ℝ)^k)*favorableBlockWidth L≤Real.exp L at ham
  refine ⟨hL,?_,by linarith,by linarith,by linarith,cell_count_cost hk hL⟩
  have hgp := hb.2.2.2.2
  nlinarith [mul_le_mul_of_nonneg_right hp hw]

end Ostmann.Construction.RepeatedPriorBounds

end

end OAI
