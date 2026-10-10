import OAI.NumberTheory.CubicMoment.Estimates.OverlapScale

namespace OAI

/-! Logarithmic height and saving normalization for an ordinary group
whose scale is at least X^(1/3). -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma largeTuple_log_comparison {X B : ℝ} (hX : 1 ≤ X)
    (hB : X^(1/3:ℝ) ≤ B) :
    (1/3:ℝ)*(1+Real.log X) ≤ 1+Real.log B := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hh := Real.log_le_log (Real.rpow_pos_of_pos hXp (1/3:ℝ)) hB
  rw [Real.log_rpow hXp] at hh
  linarith

lemma eventually_largeTuple_height_comparison (U : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ B : ℝ, X^(1/3:ℝ) ≤ B →
      (1+Real.log X)^U ≤ (1+Real.log B)^(U+1) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop ((3:ℝ)^(U+1))] with X hX hlarge
  intro B hB
  have hB1 : 1 ≤ B := (Real.one_le_rpow hX (by norm_num : (0:ℝ) ≤ 1/3)).trans hB
  have hL := largeTuple_log_comparison hX hB
  have hLX : 0 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hLB : 0 ≤ 1+Real.log B := by linarith [Real.log_nonneg hB1]
  have hinv : 1+Real.log X ≤ (3:ℝ)*(1+Real.log B) := by linarith
  have hbig : (3:ℝ)^U ≤ 1+Real.log B := by
    have he : (3:ℝ)^U = (1/3:ℝ)*(3:ℝ)^(U+1) := by
      rw [pow_succ]
      ring
    rw [he]
    nlinarith
  calc
    _ ≤ ((3:ℝ)*(1+Real.log B))^U := pow_le_pow_left₀ hLX hinv U
    _ = (3:ℝ)^U*(1+Real.log B)^U := mul_pow _ _ _
    _ ≤ (1+Real.log B)*(1+Real.log B)^U :=
      mul_le_mul_of_nonneg_right hbig (pow_nonneg hLB _)
    _ = _ := by rw [pow_succ]; ring

lemma largeTuple_bilinear_scale {X A B K : ℝ} (hX : 1 ≤ X)
    (hA : 0 ≤ A) (hB : X^(1/3:ℝ) ≤ B) (hK : 0 ≤ K)
    (hAB : A*B ≤ 3*X) (k : ℕ) :
    K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k ≤
      (K*3^(5/6:ℝ)/(1/3:ℝ)^k)*X^(5/6:ℝ)/(1+Real.log X)^k := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hB1 : 1 ≤ B := (Real.one_le_rpow hX (by norm_num : (0:ℝ) ≤ 1/3)).trans hB
  have hL := largeTuple_log_comparison hX hB
  have hLX : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hLB : 0 < 1+Real.log B := by linarith [Real.log_nonneg hB1]
  have hp := Real.rpow_le_rpow (mul_nonneg hA (zero_le_one.trans hB1)) hAB
    (by norm_num : (0:ℝ) ≤ 5/6)
  rw [Real.mul_rpow hA (zero_le_one.trans hB1),Real.mul_rpow (by norm_num) hXp.le] at hp
  calc
    _ ≤ K*(3^(5/6:ℝ)*X^(5/6:ℝ))/(1+Real.log B)^k := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg hLB.le _)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hK
    _ ≤ K*(3^(5/6:ℝ)*X^(5/6:ℝ))/((1/3:ℝ)*(1+Real.log X))^k :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos (by positivity) _)
        (pow_le_pow_left₀ (by positivity) hL k)
    _ = _ := by rw [mul_pow]; field_simp


end CubicFirstMoment

end

end OAI
