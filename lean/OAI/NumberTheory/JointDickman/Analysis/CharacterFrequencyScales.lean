import OAI.NumberTheory.JointDickman.Analysis.CharacterLFunctionCutoff

namespace OAI

/-! # Truncation scales for logarithmic character estimates -/
namespace JointDickman
open Filter
open scoped Topology

theorem character_frequency_scales {B : ℝ} (hB : 2 ≤ B) (U₀ : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∃ N K : ℕ,
      1 ≤ N ∧ U₀ ≤ (N:ℝ) ∧ (N:ℝ) ≤ T ∧
      Real.log N ≤ Real.log 2 + (1/B)*Real.log T ∧
      T ≤ (2:ℝ)^K*(N:ℝ) ∧ (2:ℝ)^K*(N:ℝ) ≤ 2*T ∧
      ((2:ℝ)^K*(N:ℝ))^(1/2:ℝ) ≤ T/(2*Real.pi) ∧
      T/(2*Real.pi) ≤ (N:ℝ)^B := by
  have hB0 : 0 < B := by linarith
  have hε : 0 < 1/B := one_div_pos.mpr hB0
  have hε1 : 1/B < 1 := (div_lt_one hB0).mpr (by linarith)
  have hpower := (tendsto_rpow_atTop hε).eventually_ge_atTop U₀
  have hgap := (tendsto_rpow_atTop (show 0 < 1-1/B by linarith)).eventually_ge_atTop 2
  filter_upwards [hpower,hgap,eventually_ge_atTop (max 1 (8*Real.pi^2))] with T hp hg hT
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hx : 1 ≤ T^(1/B) := Real.one_le_rpow hT1 hε.le
  let N : ℕ := ⌈T^(1/B)⌉₊
  have hNl : T^(1/B) ≤ (N:ℝ) := Nat.le_ceil _
  have hNu : (N:ℝ) ≤ 2*T^(1/B) := by
    have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg hT0.le (1/B))
    dsimp [N]
    linarith
  have hpow : T^(1/B)*T^(1-1/B) = T := by
    rw [←Real.rpow_add hT0]
    simp
  have hNT : (N:ℝ) ≤ T := hNu.trans (by nlinarith [Real.rpow_pos_of_pos hT0 (1/B)])
  have hN0 : (0:ℝ) < N := lt_of_lt_of_le (by positivity : 0 < T^(1/B)) hNl
  have hN1 : 1 ≤ N := by exact_mod_cast hx.trans hNl
  obtain ⟨k,hk,hk'⟩ := exists_nat_pow_near ((one_le_div hN0).mpr hNT) (by norm_num : (1:ℝ) < 2)
  have hcap : (2:ℝ)^(k+1)*(N:ℝ) ≤ 2*T := by
    rw [pow_succ]
    have hh := (le_div_iff₀ hN0).mp hk
    linarith
  have hcover : T ≤ (2:ℝ)^(k+1)*(N:ℝ) := ((div_lt_iff₀ hN0).mp hk').le
  refine ⟨N,k+1,hN1,hp.trans hNl,hNT,?_,hcover,hcap,?_,?_⟩
  · calc
      Real.log N ≤ Real.log (2*T^(1/B)) := Real.log_le_log hN0 hNu
      _ = _ := by rw [Real.log_mul (by norm_num) (by positivity),Real.log_rpow hT0]
  · rw [←Real.sqrt_eq_rpow]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hlarge : 8*Real.pi^2 ≤ T := (le_max_right _ _).trans hT
    have hsq : 2*T ≤ (T/(2*Real.pi))^2 := by
      have hpi := Real.pi_pos
      rw [div_pow]
      apply (le_div_iff₀ (sq_pos_of_pos (show 0 < 2*Real.pi by positivity))).mpr
      nlinarith [mul_nonneg hT0.le (sub_nonneg.mpr hlarge)]
    exact hcap.trans hsq
  · calc
      T/(2*Real.pi) ≤ T := div_le_self hT0.le (by nlinarith [Real.pi_gt_three])
      _ = (T^(1/B))^B := by rw [←Real.rpow_mul hT0.le, one_div_mul_cancel hB0.ne', Real.rpow_one]
      _ ≤ (N:ℝ)^B := Real.rpow_le_rpow (by positivity) hNl hB0.le

end JointDickman

end OAI
