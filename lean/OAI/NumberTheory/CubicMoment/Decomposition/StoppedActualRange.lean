import OAI.NumberTheory.CubicMoment.Estimates.FixedScalePowers
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! The actual ordinary stopped range lies strictly inside the stronger
length range needed for the full Gauss Mellin complement. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem eventually_stopped_actual_range (G : ℕ) :
    ∀ᶠ X : ℝ in atTop, ∀ A b : ℝ,
      X/16 ≤ A*b → A*b ≤ 16*X →
      X^(7/20:ℝ) ≤ b → b ≤ X^(39/100:ℝ) →
      2*b^(3/2:ℝ) ≤ A ∧ A ≤ b^2/(Real.log X)^G := by
  have hlogsave := (isLittleO_log_rpow_rpow_atTop (G:ℝ)
    (by norm_num : (0:ℝ) < 1/20)).def (by norm_num : (0:ℝ) < 1/16)
  filter_upwards [eventually_gt_atTop (1:ℝ),hlogsave,
    eventually_const_mul_rpow_le (by norm_num : (39/40:ℝ) < 1) 32]
    with X hX hlogsave hpower
  intro A b hlo hhi hblo hbhi
  have hXp : 0 < X := zero_lt_one.trans hX
  have hbp : 0 < b := (Real.rpow_pos_of_pos hXp _).trans_le hblo
  have hL : 0 < Real.log X := Real.log_pos hX
  have hlower : 2*b^(3/2:ℝ) ≤ A := by
    have hbpow := Real.rpow_le_rpow hbp.le hbhi (by norm_num : (0:ℝ) ≤ 5/2)
    rw [←Real.rpow_mul hXp.le] at hbpow
    norm_num at hbpow
    have hbsmall : 32*b^(5/2:ℝ) ≤ X :=
      (mul_le_mul_of_nonneg_left hbpow (by norm_num)).trans (by simpa only [Real.rpow_one] using hpower)
    have he : b^(3/2:ℝ)*b = b^(5/2:ℝ) := by
      calc
        _ = b^(3/2:ℝ)*b^(1:ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [←Real.rpow_add hbp]; norm_num
    apply (mul_le_mul_iff_left₀ hbp).mp
    rw [mul_assoc,he]
    exact (show 2*b^(5/2:ℝ) ≤ X/16 by linarith only [hbsmall]).trans hlo
  have hlogbound : (Real.log X)^G ≤ (1/16:ℝ)*X^(1/20:ℝ) := by
    simpa only [Real.rpow_natCast,Real.norm_of_nonneg (pow_nonneg hL.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hXp.le _)] using hlogsave
  have hbcube : X^(21/20:ℝ) ≤ b^3 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hXp.le _) hblo 3
    rw [←Real.rpow_natCast,←Real.rpow_mul hXp.le] at hh
    norm_num at hh
    exact hh
  have hmul : (A*b)*(Real.log X)^G ≤ b^3 := by
    calc
      _ ≤ (16*X)*(Real.log X)^G := mul_le_mul_of_nonneg_right hhi (pow_nonneg hL.le _)
      _ ≤ (16*X)*((1/16:ℝ)*X^(1/20:ℝ)) :=
        mul_le_mul_of_nonneg_left hlogbound (by positivity)
      _ = X^(21/20:ℝ) := by
        have he : X*X^(1/20:ℝ) = X^(21/20:ℝ) := by
          nth_rw 1 [←Real.rpow_one X]
          rw [←Real.rpow_add hXp]
          norm_num
        nlinarith [he]
      _ ≤ _ := hbcube
  refine ⟨hlower,(le_div_iff₀ (pow_pos hL G)).mpr ?_⟩
  apply (mul_le_mul_iff_left₀ hbp).mp
  nlinarith

end CubicFirstMoment

end

end OAI
