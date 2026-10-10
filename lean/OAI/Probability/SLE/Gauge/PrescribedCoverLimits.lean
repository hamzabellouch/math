import OAI.Probability.SLE.Gauge.GaugeEntrySmallness
import OAI.Probability.SLE.Gauge.CoverNumerics

namespace OAI

/-! The missed-cell error in the prescribed cover vanishes, including
the bottom rows whose centers approach the real boundary. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace SLEExactGauge

lemma prescribed_cleanup_radius_le_exp {κ : ℝ} (hκ : 0<κ) (W : Target.WienerLaw)
    {n : ℕ} (hn : 1 ≤ n) :
    Target.entryRadius κ W (n,none) ≤ Real.exp (-(n:ℝ)) := by
  refine (Target.entryRadius_le_batch_exp hκ W _).trans ?_
  apply Real.exp_le_exp.mpr
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

lemma prescribed_cover_diameter_tendsto_zero (C : ℝ) :
    Tendsto (fun n : ℕ => 8*C*Real.exp (-(n:ℝ)^2)) atTop (𝓝 0) := by
  have he : Tendsto (fun n : ℕ => Real.exp (-(n:ℝ))) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero,one_mul,neg_mul,Function.comp_def] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 1 (by norm_num)).comp
        tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun n : ℕ => Real.exp (-(n:ℝ)^2)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
    · exact Eventually.of_forall (fun _ => (Real.exp_pos _).le)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
      exact Real.exp_le_exp.mpr (by nlinarith)
  simpa only [mul_zero] using hsq.const_mul (8*C)

lemma prescribed_batch_failure_cost_tendsto_zero :
    Tendsto (fun n : ℕ => (n:ℝ)*Real.exp (-((2:ℝ)^n/16))) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)*Real.exp (-(1/16:ℝ)*(n:ℝ))) atTop (𝓝 0) := by
    simpa only [Real.rpow_one,Function.comp_def] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/16) (by norm_num)).comp
        tendsto_natCast_atTop_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact Eventually.of_forall (fun n => mul_nonneg (Nat.cast_nonneg n) (Real.exp_pos _).le)
  · apply Eventually.of_forall
    intro n
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
    apply Real.exp_le_exp.mpr
    have hn : (n:ℝ) ≤ (2:ℝ)^n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
    linarith

lemma prescribed_boundary_cost_tendsto_zero {κ : ℝ} (hκ : 0<κ) (W : Target.WienerLaw) :
    Tendsto (fun n : ℕ => (n:ℝ)*(Real.exp (-(n:ℝ))+
      Target.entryRadius κ W (n,none))^(1-codimension κ)) atTop (𝓝 0) := by
  let q := 1-codimension κ
  have hq : 0<q := by dsimp only [q,codimension,dimension]; linarith
  have ht : Tendsto (fun n : ℕ => (2:ℝ)^q*((n:ℝ)*Real.exp (-q*(n:ℝ)))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 q hq).comp
      tendsto_natCast_atTop_atTop
    simpa only [Real.rpow_one,Function.comp_def,mul_zero] using h.const_mul ((2:ℝ)^q)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · apply Eventually.of_forall
    intro n
    exact mul_nonneg (Nat.cast_nonneg n) (Real.rpow_nonneg
      (add_nonneg (Real.exp_pos _).le (show 0 ≤ Target.entryRadius κ W (n,none) from (Real.exp_pos _).le)) _)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hr := prescribed_cleanup_radius_le_exp hκ W hn
    have hrad : 0 < Target.entryRadius κ W (n,none) := Real.exp_pos _
    have hp : (Real.exp (-(n:ℝ))+Target.entryRadius κ W (n,none))^q ≤
        (2*Real.exp (-(n:ℝ)))^q := by
      apply Real.rpow_le_rpow (by positivity) (by linarith) hq.le
    have he : (2*Real.exp (-(n:ℝ)))^q = (2:ℝ)^q*Real.exp (-q*(n:ℝ)) := by
      rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le,← Real.exp_mul]
      congr 2
      ring
    rw [he] at hp
    calc
      _ ≤ (n:ℝ)*((2:ℝ)^q*Real.exp (-q*(n:ℝ))) := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg n)
      _ = _ := by ring

lemma prescribed_cleanup_error_tendsto_zero {κ : ℝ} (hκ : 0<κ) (W : Target.WienerLaw) :
    Tendsto (fun n : ℕ => (n:ℝ)*Real.exp (-((2:ℝ)^n/16)) +
      (n:ℝ)*(Real.exp (-(n:ℝ))+Target.entryRadius κ W (n,none))^(1-codimension κ))
        atTop (𝓝 0) := by
  simpa only [add_zero] using prescribed_batch_failure_cost_tendsto_zero.add
    (prescribed_boundary_cost_tendsto_zero hκ W)

end SLEExactGauge

end

end OAI
