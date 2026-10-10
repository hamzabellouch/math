import OAI.NumberTheory.TwoPoint.Walks.WitnessScaleParameters

namespace OAI

/-! Elementary bounds for the actual trace and witness lengths. -/

namespace TwoPointCorrelations

open Filter

lemma eventually_trace_slot_budgets (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ k J M : ℕ,
      (k : ℝ) ≤ L → (J + M : ℕ) ≤ C * Real.log L →
      ((⌊L ^ (1 / 4 : ℝ)⌋₊ + 2 * k * J : ℕ) : ℝ) ≤
          (2 * C + 1) * L * Real.log L ∧
      ((2 * k * (J + M) : ℕ) : ℝ) + 1 ≤ L ^ 2 ∧
      ((2 * k : ℕ) : ℝ) + 1 ≤ L ^ 2 := by
  have hs := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).bound
    (show 0 < 1 / (4 * (C + 1)) by positivity)
  filter_upwards [eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1), hs] with L hL hlog hs
  intro k J M hk hJM
  have hLp : 0 < L := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ Real.log L),
    Real.norm_eq_abs, Real.rpow_one, abs_of_pos hLp] at hs
  have hs' : 4 * (C + 1) * Real.log L ≤ L := by
    have ht : Real.log L ≤ L / (4 * (C + 1)) := by
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using hs
    have ht' := (le_div_iff₀ (show 0 < 4 * (C + 1) by positivity)).mp ht
    nlinarith
  have hJ : (J : ℝ) ≤ C * Real.log L := by
    exact (show (J : ℝ) ≤ (J + M : ℕ) by exact_mod_cast Nat.le_add_right J M).trans hJM
  have hf : (⌊L ^ (1 / 4 : ℝ)⌋₊ : ℝ) ≤ L := by
    apply (Nat.floor_le (Real.rpow_nonneg hLp.le _)).trans
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ L)
      (show (1 / 4 : ℝ) ≤ 1 by norm_num)
  have hprod : (2 * k * J : ℕ) ≤ 2 * L * (C * Real.log L) := by
    push_cast
    exact mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num)) hJ
      (by positivity) (by positivity)
  have hprod' : (2 * k * (J + M) : ℕ) ≤ 2 * L * (C * Real.log L) := by
    push_cast at hJM ⊢
    exact mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num)) hJM
      (by positivity) (by positivity)
  have hCL : C * Real.log L ≤ L / 4 := by nlinarith
  have hlogL : L ≤ L * Real.log L := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · push_cast
    nlinarith
  · have hm := mul_le_mul_of_nonneg_left hCL (show 0 ≤ 2 * L by positivity)
    nlinarith
  · push_cast
    nlinarith

lemma eventually_trace_witness_budgets (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop,
      L / 2 ≤ (⌊L⌋₊ : ℝ) ∧ (⌊L⌋₊ : ℝ) ≤ L ∧
      0 < ⌊L ^ (1 / 10 : ℝ)⌋₊ ∧
      L ^ (1 / 10 : ℝ) / 2 ≤ (⌊L ^ (1 / 10 : ℝ)⌋₊ : ℝ) ∧
      0 < ⌊L ^ (1 / 12 : ℝ)⌋₊ ∧
      (⌊L ^ (1 / 12 : ℝ)⌋₊ : ℝ) ≤ 4 * L ∧
      8 * (⌊L ^ (1 / 12 : ℝ)⌋₊ / 8) ≤ ⌊L ^ (1 / 12 : ℝ)⌋₊ ∧
      L ^ (1 / 12 : ℝ) / 32 ≤ ((⌊L ^ (1 / 12 : ℝ)⌋₊ / 8 : ℕ) : ℝ) ∧
      ((⌊L ^ (1 / 12 : ℝ)⌋₊ / 8 : ℕ) : ℝ) ≤ L ∧
      ((2 * ⌊L⌋₊ + ⌊L ^ (1 / 12 : ℝ)⌋₊ * ⌊L ^ (1 / 10 : ℝ)⌋₊ : ℕ) : ℝ) ≤ 4 * L ∧
      ∀ J S : ℕ, (J : ℝ) ≤ C * Real.log L → ⌊L ^ (1 / 4 : ℝ)⌋₊ < S →
        ⌊L ^ (1 / 12 : ℝ)⌋₊ * (⌊L ^ (1 / 10 : ℝ)⌋₊ * J) < S := by
  have hs := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num)).eventually
    (eventually_ge_atTop 2)
  have hn := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 12 by norm_num)).eventually
    (eventually_ge_atTop 2)
  filter_upwards [eventually_ge_atTop (2 : ℝ), hs, hn,
    eventually_singleton_floor_bounds, eventually_witness_cover_budget C hC] with
    L hL hs hn hfloor hcover
  have hLp : 0 < L := by linarith
  have hk : (⌊L⌋₊ : ℝ) ≤ L := Nat.floor_le hLp.le
  have hklo : L / 2 ≤ (⌊L⌋₊ : ℝ) := by
    have ht := Nat.lt_floor_add_one L
    linarith
  have hslo : L ^ (1 / 10 : ℝ) / 2 ≤ (⌊L ^ (1 / 10 : ℝ)⌋₊ : ℝ) := by
    have ht := Nat.lt_floor_add_one (L ^ (1 / 10 : ℝ))
    linarith
  have hspos : 0 < ⌊L ^ (1 / 10 : ℝ)⌋₊ := by
    have ht : (0 : ℝ) < (⌊L ^ (1 / 10 : ℝ)⌋₊ : ℝ) := by linarith
    exact_mod_cast ht
  have hnpos : 0 < ⌊L ^ (1 / 12 : ℝ)⌋₊ := by
    have ht := Nat.lt_floor_add_one (L ^ (1 / 12 : ℝ))
    have hp : (0 : ℝ) < (⌊L ^ (1 / 12 : ℝ)⌋₊ : ℝ) := by linarith
    exact_mod_cast hp
  have hnhi : (⌊L ^ (1 / 12 : ℝ)⌋₊ : ℝ) ≤ 4 * L := by
    have hp : L ^ (1 / 12 : ℝ) ≤ L := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ L)
        (show (1 / 12 : ℝ) ≤ 1 by norm_num)
    have ht := Nat.floor_le (Real.rpow_nonneg hLp.le (1 / 12 : ℝ))
    linarith
  have hsbound := Nat.floor_le (Real.rpow_nonneg hLp.le (1 / 10 : ℝ))
  have hR : ((2 * ⌊L⌋₊ : ℕ) : ℝ) ≤ 2 * L := by push_cast; linarith
  have hD := (hcover ⌊L ^ (1 / 10 : ℝ)⌋₊ 0 (⌊L ^ (1 / 4 : ℝ)⌋₊ + 1)
    (2 * ⌊L⌋₊) hsbound (by simpa using mul_nonneg hC (Real.log_nonneg (by linarith)))
    (by simpa using Nat.lt_floor_add_one (L ^ (1 / 4 : ℝ))) hR).2
  refine ⟨hklo, hk, hspos, hslo, hnpos, hnhi, Nat.mul_div_le _ _,
    hfloor.1, hfloor.2, hD, ?_⟩
  intro J S hJ hS
  apply (hcover _ J S _ hsbound hJ _ hR).1
  exact (Nat.floor_lt (Real.rpow_nonneg hLp.le _)).mp hS

end TwoPointCorrelations

end OAI
