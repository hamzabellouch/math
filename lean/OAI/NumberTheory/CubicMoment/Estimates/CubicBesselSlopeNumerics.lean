import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselSlopeLower
import Mathlib.Analysis.Complex.ExponentialBounds

namespace OAI

/-! Rational bounds used only for the first nonzero theta frequency. -/
noncomputable section
namespace CubicFirstMoment

lemma cubic_exp_one_le : Real.exp 1≤87/32 := by
  linarith [Real.exp_one_lt_d9]

lemma cubic_cosh_half_le : Real.cosh (1/2:ℝ)≤8/7 := by
  have hc := Real.cosh_le_exp_half_sq (1/2:ℝ)
  have he := Real.exp_bound_div_one_sub_of_interval (x:=(1/8:ℝ)) (by norm_num) (by norm_num)
  norm_num at hc he ⊢
  exact hc.trans he

lemma cubic_cosh_one_le : Real.cosh (1:ℝ)≤8/5 := by
  rw [Real.cosh_eq]
  linarith [Real.exp_one_lt_d9,Real.exp_neg_one_lt_d9]

lemma cubic_cosh_three_halves_le : Real.cosh (3/2:ℝ)≤12/5 := by
  have he3 : Real.exp (3:ℝ)≤(87/32:ℝ)^3 := by
    calc
      _ = Real.exp 1^3 := by norm_num [←Real.exp_nat_mul]
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le cubic_exp_one_le 3
  have he : Real.exp (3/2:ℝ)≤9/2 := by
    have hsq : Real.exp (3/2:ℝ)^2=Real.exp 3 := by
      rw [←Real.exp_nat_mul]
      norm_num
    nlinarith [Real.exp_pos (3/2:ℝ)]
  have hepos : (4:ℝ)≤Real.exp (3/2:ℝ) := by
    have h1 : (8/3:ℝ)≤Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hhalf : (3/2:ℝ)≤Real.exp (1/2:ℝ) := by linarith [Real.add_one_le_exp (1/2:ℝ)]
    calc
      _ ≤ Real.exp 1*Real.exp (1/2:ℝ) := by nlinarith [Real.exp_pos (1:ℝ)]
      _ = Real.exp (3/2:ℝ) := by rw [←Real.exp_add]; norm_num
  have heneg : Real.exp (-(3/2:ℝ))≤1/4 := by
    rw [Real.exp_neg]
    apply (inv_le_comm₀ (Real.exp_pos _) (by norm_num)).mpr
    norm_num
    exact hepos
  rw [Real.cosh_eq]
  linarith

lemma cubic_exp_three_le : Real.exp (3:ℝ)≤21 := by
  have h := pow_le_pow_left₀ (Real.exp_pos _).le cubic_exp_one_le 3
  rw [←Real.exp_nat_mul] at h
  norm_num at h
  linarith

lemma cubic_exp_four_le : Real.exp (4:ℝ)≤55 := by
  have h := pow_le_pow_left₀ (Real.exp_pos _).le cubic_exp_one_le 4
  rw [←Real.exp_nat_mul] at h
  norm_num at h
  linarith

lemma cubic_exp_six_le : Real.exp (6:ℝ)≤405 := by
  have h := pow_le_pow_left₀ (Real.exp_pos _).le cubic_exp_one_le 6
  rw [←Real.exp_nat_mul] at h
  norm_num at h
  linarith

end CubicFirstMoment

end

end OAI
