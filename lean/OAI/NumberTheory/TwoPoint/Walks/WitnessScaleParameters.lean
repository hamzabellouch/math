import OAI.NumberTheory.TwoPoint.Bounds.SingletonDecay

namespace OAI

/-! The actual singleton threshold supplies enough short witnesses within the trace length budget. -/

namespace TwoPointCorrelations

open Filter

lemma eventually_witness_cover_budget (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (s J S R : ℕ),
      (s : ℝ) ≤ L ^ (1 / 10 : ℝ) → (J : ℝ) ≤ C * Real.log L →
      L ^ (1 / 4 : ℝ) < S → (R : ℝ) ≤ 2 * L →
      ⌊L ^ (1 / 12 : ℝ)⌋₊ * (s * J) < S ∧
      ((R + ⌊L ^ (1 / 12 : ℝ)⌋₊ * s : ℕ) : ℝ) ≤ 4 * L := by
  have hsmall := (isLittleO_log_rpow_atTop (show 0 < (1 / 15 : ℝ) by norm_num)).bound
    (show 0 < 1 / (2 * (C + 1)) by positivity)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall] with L hL hslog
  intro s J S R hs hJ hS hR
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  rw [Real.norm_eq_abs, abs_of_nonneg hlog, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hLp _)] at hslog
  have hslog' : Real.log L ≤ L ^ (1 / 15 : ℝ) / (2 * (C + 1)) := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hslog
  have hlogmul := (le_div_iff₀ (show 0 < 2 * (C + 1) by positivity)).mp hslog'
  have hcoeff : C * Real.log L < L ^ (1 / 15 : ℝ) := by
    have hp := Real.rpow_pos_of_pos hLp (1 / 15 : ℝ)
    nlinarith
  have hT : (⌊L ^ (1 / 12 : ℝ)⌋₊ : ℝ) ≤ L ^ (1 / 12 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hLp.le _)
  have hTs : ((⌊L ^ (1 / 12 : ℝ)⌋₊ * s : ℕ) : ℝ) ≤ L ^ (11 / 60 : ℝ) := by
    push_cast
    calc
      _ ≤ L ^ (1 / 12 : ℝ) * L ^ (1 / 10 : ℝ) :=
        mul_le_mul hT hs (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add hLp]; norm_num
  have hcover : ((⌊L ^ (1 / 12 : ℝ)⌋₊ * (s * J) : ℕ) : ℝ) < S := by
    calc
      _ = ((⌊L ^ (1 / 12 : ℝ)⌋₊ * s : ℕ) : ℝ) * J := by push_cast; ring
      _ ≤ L ^ (11 / 60 : ℝ) * (C * Real.log L) :=
        mul_le_mul hTs hJ (by positivity) (by positivity)
      _ < L ^ (11 / 60 : ℝ) * L ^ (1 / 15 : ℝ) :=
        mul_lt_mul_of_pos_left hcoeff (Real.rpow_pos_of_pos hLp _)
      _ = L ^ (1 / 4 : ℝ) := by rw [← Real.rpow_add hLp]; norm_num
      _ < S := hS
  refine ⟨by exact_mod_cast hcover, ?_⟩
  have hpow : L ^ (11 / 60 : ℝ) ≤ L := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL (show (11 / 60 : ℝ) ≤ 1 by norm_num)
  push_cast at hTs ⊢
  linarith

end TwoPointCorrelations

end OAI
