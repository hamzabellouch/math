import OAI.NumberTheory.JointDickman.Counting.CoefficientPartialSum

namespace OAI

/-! # Subpower loss in the rough coefficient normalization -/

namespace JointDickman
open Filter
open scoped Topology

theorem coefficientScale_power {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ B : ℕ in atTop, coefficientScale B ≤ (B : ℝ)^(1/2+ε) := by
  have hsmall : ∀ᶠ B : ℕ in atTop,
      (1000 : ℝ)^(1/2 : ℝ)*(Real.log B)^(1/2 : ℝ)/(B : ℝ)^ε ≤ 1 := by
    have hh := ((log_power_div_power_tendsto_zero (1/2) hε).const_mul
      ((1000 : ℝ)^(1/2 : ℝ))).comp tendsto_natCast_atTop_atTop
    have hz : (1000 : ℝ)^(1/2 : ℝ)*0 = 0 := mul_zero _
    rw [hz] at hh
    filter_upwards [hh.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))] with B hB
    simpa only [Function.comp_def,mul_div_assoc] using hB
  filter_upwards [hsmall,eventually_gt_atTop 1] with B hsmallB hB
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hl : 0 < Real.log (auxiliaryCutoff B) := by
    simp only [auxiliaryCutoff,Nat.cast_pow,Real.log_pow]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hB))
  have hr : auxiliaryRatio B = (B : ℝ)/Real.log (auxiliaryCutoff B) := by
    simp [auxiliaryRatio,auxiliaryCutoff,Nat.cast_pow,Real.log_pow]
  have hlog : Real.log (auxiliaryCutoff B)^(1/2 : ℝ) ≤ (B : ℝ)^ε := by
    simp only [auxiliaryCutoff,Nat.cast_pow,Real.log_pow,Nat.cast_ofNat]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1000) (Real.log_natCast_nonneg B)]
    exact (div_le_one (Real.rpow_pos_of_pos hB0 ε)).mp hsmallB
  have hid : coefficientScale B =
      (B : ℝ)^(1/2 : ℝ)*Real.log (auxiliaryCutoff B)^(1/2 : ℝ) := by
    unfold coefficientScale
    rw [hr,Real.div_rpow hB0.le hl.le]
    have he : Real.log (auxiliaryCutoff B)/Real.log (auxiliaryCutoff B)^(1/2 : ℝ) =
        Real.log (auxiliaryCutoff B)^(1/2 : ℝ) := by
      calc
        _ = Real.log (auxiliaryCutoff B)^(1 : ℝ)/Real.log (auxiliaryCutoff B)^(1/2 : ℝ) := by
          rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_sub hl]; norm_num
    calc
      _ = (B : ℝ)^(1/2 : ℝ)*
          (Real.log (auxiliaryCutoff B)/Real.log (auxiliaryCutoff B)^(1/2 : ℝ)) := by ring
      _ = _ := by rw [he]
  rw [hid,Real.rpow_add hB0]
  exact mul_le_mul_of_nonneg_left hlog (by positivity)

end JointDickman

end OAI
