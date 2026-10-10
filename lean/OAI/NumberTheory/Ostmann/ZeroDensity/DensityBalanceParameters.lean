import OAI.NumberTheory.Ostmann.ZeroDensity.DensityMomentCutoff

namespace OAI

/-! # The conductor-height parameters in the two zero-detector estimates -/

namespace Ostmann

noncomputable def densityTargetExponent (σ : ℝ) : ℝ := 3 * (1 - σ) / (2 - σ)
noncomputable def densityBalanceExponent (σ : ℝ) : ℝ := 3 / (2 * (2 - σ))

 theorem density_conductor_height_log (Q : ℕ) (hQ : 1 ≤ Q) (T : ℝ) (hT : 2 ≤ T) :
    Real.log ((Q : ℝ) ^ 2 * T) ≤ 2 * Real.log ((Q : ℝ) * T) := by
  have hq : (0 : ℝ) < Q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hQ)
  have ht : 0 < T := by linarith
  rw [Real.log_mul (by positivity) ht.ne', Real.log_pow,
    Real.log_mul hq.ne' ht.ne']
  have hl : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  norm_num only [Nat.cast_ofNat]
  linarith

 theorem density_detector_cutoff (Q : ℕ) (hQ : 1 ≤ Q) (T : ℝ) (hT : 2 ≤ T) :
    ∃ X : ℕ, 1 ≤ X ∧ (Q : ℝ) ^ 2 * T ≤ X ∧
      (X : ℝ) + (Q : ℝ) ^ 2 * T ≤ 17 * ((Q : ℝ) ^ 2 * T) ∧
      1 + Real.log X ≤ 20 * Real.log ((Q : ℝ) * T) := by
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hB : 2 ≤ (Q : ℝ) ^ 2 * T := by nlinarith
  obtain ⟨X, hX, hlX, hscale, hsize, hlog⟩ := density_moment_cutoff 1 (by decide) ((Q : ℝ) ^ 2 * T) hB
  norm_num at hscale hsize hlog
  refine ⟨X, hX, by nlinarith, hsize, ?_⟩
  have hlB := density_conductor_height_log Q hQ T hT
  linarith

 theorem density_balance_at_least_one (σ : ℝ) (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    1 ≤ densityBalanceExponent σ := by
  unfold densityBalanceExponent
  apply (le_div_iff₀ (by linarith : 0 < 2 * (2 - σ))).mpr
  linarith

 theorem density_balance_identity (B σ : ℝ) (hB : 0 < B) (hσ : σ < 2) :
    B ^ 3 * (B ^ densityBalanceExponent σ) ^ (2 - 4 * σ) =
      (B ^ densityTargetExponent σ) ^ (3 : ℕ) := by
  rw [← Real.rpow_natCast B 3, ← Real.rpow_natCast (B ^ densityTargetExponent σ) 3,
    ← Real.rpow_mul hB.le, ← Real.rpow_mul hB.le, ← Real.rpow_add hB]
  congr 1
  unfold densityTargetExponent densityBalanceExponent
  have hd : 2 - σ ≠ 0 := by linarith
  field_simp [hd]
  ring

 theorem density_away_inverse_gap (Q : ℕ) (hQ : 1 ≤ Q) (T σ : ℝ) (hT : 2 ≤ T)
    (hσ : 1 / 2 < σ) (hgap : 1 / Real.log ((Q : ℝ) ^ 2 * T) ≤ σ - 1 / 2) :
    1 / (σ - 1 / 2) ≤ 2 * Real.log ((Q : ℝ) * T) := by
  have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hB : 1 < (Q : ℝ) ^ 2 * T := by nlinarith
  have hl : 0 < Real.log ((Q : ℝ) ^ 2 * T) := Real.log_pos hB
  have hh := mul_le_mul_of_nonneg_right hgap hl.le
  rw [div_mul_cancel₀ _ hl.ne'] at hh
  apply (div_le_iff₀ (by linarith : 0 < σ - 1 / 2)).mpr
  have hlog := density_conductor_height_log Q hQ T hT
  nlinarith

 theorem density_balanced_count_from_cube (C R B σ L : ℝ) (hC : 0 ≤ C)
    (hR : 0 ≤ R) (hB : 0 ≤ B)
    (h : R ^ 3 ≤ C * (B ^ densityTargetExponent σ) ^ 3 * L ^ 12) :
    R ≤ (C + 1) * B ^ densityTargetExponent σ * L ^ 4 := by
  have hc : C ≤ (C + 1) ^ 3 := by nlinarith [sq_nonneg C]
  have hh : R ^ 3 ≤ ((C + 1) * B ^ densityTargetExponent σ * L ^ 4) ^ 3 := by
    apply h.trans
    have hm := mul_le_mul_of_nonneg_right hc
      (show 0 ≤ (B ^ densityTargetExponent σ) ^ 3 * L ^ 12 by positivity)
    convert hm using 1 <;> ring
  exact (pow_le_pow_iff_left₀ hR (by positivity) (by decide : (3 : ℕ) ≠ 0)).mp hh

end Ostmann

end OAI
