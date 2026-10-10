import OAI.NumberTheory.Ostmann.Preliminaries.CollisionStability

namespace OAI

open Erdos970

namespace Ostmann.Preliminaries
open scoped BigOperators
open Filter

noncomputable def collisionScale (b X : ℕ) : ℕ :=
  ⌊Real.sqrt X / Real.log (X : ℝ) ^ (b + 1)⌋₊

noncomputable def collisionMassCap (b X : ℕ) : ℝ :=
  Real.log (X : ℝ) ^ b / Real.sqrt X

theorem collisionScale_estimates (b X : ℕ) (hX : 0 < X)
    (hlog : 1 ≤ Real.log (X : ℝ))
    (hscale : 2 ≤ Real.sqrt X / Real.log (X : ℝ) ^ (b + 1)) :
    1 ≤ collisionScale b X ∧
    Real.log (X : ℝ) / 2 - (b + 1 : ℕ) * Real.log (Real.log (X : ℝ)) - Real.log 2 ≤
      Real.log (collisionScale b X : ℝ) ∧
    (collisionScale b X : ℝ) * collisionMassCap b X ≤ 1 := by
  have hxr : (0 : ℝ) < X := by exact_mod_cast hX
  have hl : 0 < Real.log (X : ℝ) := by linarith
  have hsqrt : 0 < Real.sqrt X := Real.sqrt_pos.mpr hxr
  have hpow : 0 < Real.log (X : ℝ) ^ (b + 1) := pow_pos hl _
  have ht : 0 < Real.sqrt X / Real.log (X : ℝ) ^ (b + 1) := div_pos hsqrt hpow
  have hfloor := Nat.lt_floor_add_one (Real.sqrt X / Real.log (X : ℝ) ^ (b + 1))
  have hhalf : (Real.sqrt X / Real.log (X : ℝ) ^ (b + 1)) / 2 ≤ collisionScale b X := by
    unfold collisionScale
    linarith
  refine ⟨(Nat.one_le_floor_iff _).mpr (by linarith), ?_, ?_⟩
  · have h := Real.log_le_log (div_pos ht (by norm_num)) hhalf
    rw [Real.log_div (ne_of_gt ht) (by norm_num),
      Real.log_div (ne_of_gt hsqrt) (ne_of_gt hpow),
      Real.log_sqrt hxr.le, Real.log_pow] at h
    exact h
  · have hf : (collisionScale b X : ℝ) ≤
        Real.sqrt X / Real.log (X : ℝ) ^ (b + 1) := Nat.floor_le ht.le
    have hm : 0 ≤ collisionMassCap b X := div_nonneg (pow_nonneg hl.le _) hsqrt.le
    have hid : (Real.sqrt X / Real.log (X : ℝ) ^ (b + 1)) * collisionMassCap b X =
        (Real.log (X : ℝ))⁻¹ := by
      unfold collisionMassCap
      rw [pow_succ]
      field_simp
    exact (mul_le_mul_of_nonneg_right hf hm).trans
      (by rw [hid]; exact inv_le_one_of_one_le₀ hlog)

theorem collisionScale_error_le (b X : ℕ) (hX : 0 < X)
    (hlog : 1 ≤ Real.log (X : ℝ))
    (hscale : 2 ≤ Real.sqrt X / Real.log (X : ℝ) ^ (b + 1)) :
    2 * Real.log X - 4 * Real.log (collisionScale b X : ℝ) +
      2 * Real.log 4 * (collisionScale b X : ℝ) * collisionMassCap b X + 4 * (Real.log 4 + 4) ≤
      4 * (b + 1 : ℕ) * Real.log (Real.log (X : ℝ)) +
        (4 * Real.log 2 + 6 * Real.log 4 + 16) := by
  obtain ⟨_, hlogQ, hmass⟩ := collisionScale_estimates b X hX hlog hscale
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hcap := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 2 * Real.log 4 by positivity)
  nlinarith

theorem eventually_collisionScale_conditions (b : ℕ) :
    ∀ᶠ X : ℕ in atTop, 0 < X ∧ 1 ≤ Real.log (X : ℝ) ∧
      2 ≤ Real.sqrt X / Real.log (X : ℝ) ^ (b + 1) := by
  have hx : Tendsto (fun X : ℕ => (X : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlittle := isLittleO_log_rpow_rpow_atTop (b + 1 : ℕ) (show (0 : ℝ) < 1 / 2 by norm_num)
  have hbound := hlittle.bound (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [hx.eventually hbound, (Real.tendsto_log_atTop.comp hx).eventually_ge_atTop 1,
    eventually_gt_atTop 0] with X hsmall hlog hX
  change 1 ≤ Real.log (X : ℝ) at hlog
  refine ⟨hX, hlog, ?_⟩
  have hxr : (0 : ℝ) < X := by exact_mod_cast hX
  have hl : 0 < Real.log (X : ℝ) := by linarith
  simp only [Real.rpow_natCast, ← Real.sqrt_eq_rpow, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hl.le _), abs_of_nonneg (Real.sqrt_nonneg _)] at hsmall
  apply (le_div_iff₀ (pow_pos hl _)).mpr
  linarith

end Ostmann.Preliminaries

end OAI
