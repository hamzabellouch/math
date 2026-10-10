import OAI.NumberTheory.CubicMoment.Estimates.LargeTupleLogScale
import OAI.NumberTheory.CubicMoment.Estimates.LowHeightLogIntegral

namespace OAI

/-! The largest coordinate of a triple has a fixed power lower bound.
These normalizations preserve the fractional logarithmic saving. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma triple_log_comparison {X B : ℝ} (hX : 1 ≤ X)
    (hB : X^(1/4:ℝ) ≤ B) :
    (1/4:ℝ)*(1+Real.log X) ≤ 1+Real.log B := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hh := Real.log_le_log (Real.rpow_pos_of_pos hXp (1/4:ℝ)) hB
  rw [Real.log_rpow hXp] at hh
  linarith

lemma eventually_triple_height_comparison (U : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ B : ℝ, X^(1/4:ℝ) ≤ B →
      (1+Real.log X)^U ≤ (1+Real.log B)^(U+1) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop ((4:ℝ)^(U+1))] with X hX hlarge
  intro B hB
  have hB1 : 1 ≤ B := (Real.one_le_rpow hX (by norm_num : (0:ℝ) ≤ 1/4)).trans hB
  have hL := triple_log_comparison hX hB
  have hLX : 0 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hLB : 0 ≤ 1+Real.log B := by linarith [Real.log_nonneg hB1]
  have hinv : 1+Real.log X ≤ (4:ℝ)*(1+Real.log B) := by linarith
  have hbig : (4:ℝ)^U ≤ 1+Real.log B := by
    have he : (4:ℝ)^U = (1/4:ℝ)*(4:ℝ)^(U+1) := by rw [pow_succ]; ring
    rw [he]
    nlinarith
  calc
    _ ≤ ((4:ℝ)*(1+Real.log B))^U := pow_le_pow_left₀ hLX hinv U
    _ = (4:ℝ)^U*(1+Real.log B)^U := mul_pow _ _ _
    _ ≤ (1+Real.log B)*(1+Real.log B)^U :=
      mul_le_mul_of_nonneg_right hbig (pow_nonneg hLB _)
    _ = _ := by rw [pow_succ]; ring

lemma triple_transition_scale {X A B K : ℝ} (hX : 1 ≤ X)
    (hA : 0 ≤ A) (hB : X^(1/4:ℝ) ≤ B) (hK : 0 ≤ K)
    (hAB : A*B ≤ 3*X) :
    K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^(3/2:ℝ) ≤
      (K*3^(5/6:ℝ)/(1/4:ℝ)^(3/2:ℝ))*X^(5/6:ℝ)/(1+Real.log X)^(3/2:ℝ) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hB1 : 1 ≤ B := (Real.one_le_rpow hX (by norm_num : (0:ℝ) ≤ 1/4)).trans hB
  have hL := triple_log_comparison hX hB
  have hLX : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hLB : 0 < 1+Real.log B := by linarith [Real.log_nonneg hB1]
  have hp := Real.rpow_le_rpow (mul_nonneg hA (zero_le_one.trans hB1)) hAB
    (by norm_num : (0:ℝ) ≤ 5/6)
  rw [Real.mul_rpow hA (zero_le_one.trans hB1),Real.mul_rpow (by norm_num) hXp.le] at hp
  calc
    _ ≤ K*(3^(5/6:ℝ)*X^(5/6:ℝ))/(1+Real.log B)^(3/2:ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hK
    _ ≤ K*(3^(5/6:ℝ)*X^(5/6:ℝ))/((1/4:ℝ)*(1+Real.log X))^(3/2:ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (Real.rpow_le_rpow (by positivity) hL (by norm_num))
    _ = _ := by rw [Real.mul_rpow (by norm_num) hLX.le]; ring

lemma lowHeight_log_power_bound {Z : ℝ} (hZ : 1 ≤ Z) (n : ℕ) :
    Real.log (1+(4/3:ℝ)*Z^n) ≤ ((n:ℝ)+2)*(1+Real.log Z) := by
  have hp : 0 < Z := zero_lt_one.trans_le hZ
  have hz : 1 ≤ Z^n := one_le_pow₀ hZ
  have hh := Real.log_le_log (by positivity : 0 < 1+(4/3:ℝ)*Z^n)
    (show 1+(4/3:ℝ)*Z^n ≤ (7/3:ℝ)*Z^n by nlinarith)
  rw [Real.log_mul (by norm_num : (7/3:ℝ) ≠ 0) (pow_pos hp n).ne',Real.log_pow] at hh
  have hc := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 7/3)
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  nlinarith [Real.log_nonneg hZ]

lemma triple_bilinear_nat_scale {X A B K : ℝ} (hX : 1 ≤ X)
    (hA : 0 ≤ A) (hB : X^(1/4:ℝ) ≤ B) (hK : 0 ≤ K)
    (hAB : A*B ≤ 3*X) (k : ℕ) :
    K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k ≤
      (K*3^(5/6:ℝ)/(1/4:ℝ)^k)*X^(5/6:ℝ)/(1+Real.log X)^k := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hB1 : 1 ≤ B := (Real.one_le_rpow hX (by norm_num : (0:ℝ) ≤ 1/4)).trans hB
  have hL := triple_log_comparison hX hB
  have hLX : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hLB : 0 < 1+Real.log B := by linarith [Real.log_nonneg hB1]
  have hp := Real.rpow_le_rpow (mul_nonneg hA (zero_le_one.trans hB1)) hAB
    (by norm_num : (0:ℝ) ≤ 5/6)
  rw [Real.mul_rpow hA (zero_le_one.trans hB1),Real.mul_rpow (by norm_num) hXp.le] at hp
  calc
    _ ≤ K*(3^(5/6:ℝ)*X^(5/6:ℝ))/(1+Real.log B)^k := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hLB.le _)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hK
    _ ≤ K*(3^(5/6:ℝ)*X^(5/6:ℝ))/((1/4:ℝ)*(1+Real.log X))^k :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos (by positivity) _)
        (pow_le_pow_left₀ (by positivity) hL k)
    _ = _ := by rw [mul_pow]; field_simp


end CubicFirstMoment

end

end OAI
