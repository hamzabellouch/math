import OAI.NumberTheory.JointDickman.Analysis.MellinLastBandGrowth

namespace OAI

/-! # The endpoint range needed by the growing prime moment -/
namespace JointDickman
open Filter
open scoped Topology

theorem mellin_endpoint_scales : ∀ᶠ X : ℝ in atTop, ∀ L : ℝ,
    Real.exp ((Real.log X)^(1/4:ℝ)-1) ≤ L → L ≤ Real.exp (Real.sqrt (Real.log X)) →
    let M := ⌈2*L⌉₊
    2 ≤ M ∧ 1 ≤ Real.log (M:ℝ) ∧ (Real.log X)^100 ≤ (M:ℝ) ∧
      (M:ℝ) ≤ X^(1/100:ℝ) := by
  have hpow := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp Real.tendsto_log_atTop
  have hlim : Tendsto (fun X : ℝ => 100*Real.log (Real.log X)/(Real.log X)^(1/4:ℝ))
      atTop (𝓝 0) := by
    have hh := ((log_power_div_power_tendsto_zero 1 (by norm_num : (0:ℝ)<1/4)).comp
      Real.tendsto_log_atTop).const_mul 100
    simpa only [Function.comp_def,Real.rpow_one,mul_zero,mul_div_assoc] using hh
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop 100000),
    hpow.eventually (eventually_ge_atTop 2),
    hlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/2)),
    eventually_gt_atTop (0:ℝ)] with X hlog hpowX hlimX hX
  change 2 ≤ (Real.log X)^(1/4:ℝ) at hpowX
  intro L hLlo hLhi M
  have hlog0 : 0 < Real.log X := by linarith
  have hp0 : 0 < (Real.log X)^(1/4:ℝ) := Real.rpow_pos_of_pos hlog0 _
  have hb := (div_le_iff₀ hp0).mp hlimX
  have hlowlog : 100*Real.log (Real.log X) ≤ (Real.log X)^(1/4:ℝ)-1 := by
    linarith
  have hLe : Real.exp 1 ≤ L := (Real.exp_le_exp.mpr (by linarith)).trans hLlo
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans hLe
  have hMlo : 2*L ≤ (M:ℝ) := Nat.le_ceil _
  have hMhi : (M:ℝ) ≤ 3*L := by
    have hh := Nat.ceil_lt_add_one (show 0≤2*L by positivity)
    dsimp [M]
    linarith
  have hM0 : 0 < (M:ℝ) := by linarith
  refine ⟨by exact_mod_cast (show (2:ℝ)≤M by linarith),?_,?_,?_⟩
  · have hh := Real.log_le_log (Real.exp_pos 1) (hLe.trans (by linarith : L≤(M:ℝ)))
    simpa only [Real.log_exp] using hh
  · have he : (Real.log X)^100 = Real.exp (100*Real.log (Real.log X)) := by
      rw [show Real.exp (100*Real.log (Real.log X)) =
        (Real.exp (Real.log (Real.log X)))^100 by
          simpa using Real.exp_nat_mul (Real.log (Real.log X)) 100,
        Real.exp_log hlog0]
    rw [he]
    exact ((Real.exp_le_exp.mpr hlowlog).trans hLlo).trans (by linarith)
  · have hs : Real.sqrt (Real.log X) ≤ Real.log X/200 := by
      apply (Real.sqrt_le_iff).mpr
      constructor
      · positivity
      · have hm := mul_nonneg (show 0≤Real.log X-40000 by linarith) hlog0.le
        nlinarith
    have hlog3 : Real.log 3 ≤ 2 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
      linarith
    have he : 3*Real.exp (Real.sqrt (Real.log X)) ≤ X^(1/100:ℝ) := by
      rw [Real.rpow_def_of_pos hX,show (3:ℝ)=Real.exp (Real.log 3) by
        rw [Real.exp_log (by norm_num : (0:ℝ)<3)],← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    exact hMhi.trans ((mul_le_mul_of_nonneg_left hLhi (by norm_num)).trans he)

end JointDickman

end OAI
