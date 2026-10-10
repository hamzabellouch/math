import OAI.NumberTheory.Ostmann.Construction.InitialRepeatRate
import OAI.NumberTheory.Ostmann.Construction.InitialEndpointRate

namespace OAI

/-! # Choosing the initial gap without changing the endpoint rate -/

namespace Ostmann

open Filter
open scoped BigOperators

theorem initial_repeat_coefficient (a z A C : ℝ) (c : ℕ)
    (ha : 0 < a) (hz : 1 ≤ z) (hC : 0 ≤ C) (hc : 4 * c * A ≤ z) :
    2 * Real.log (3 * z / a) + 2 + (4 * c * A + 2 * C) / z ≤
      2 * Real.log z + (2 * Real.log (3 / a) + 3 + 2 * C) := by
  have hz0 : 0 < z := by linarith
  have hr : (4 * c * A + 2 * C) / z ≤ 1 + 2 * C := by
    apply (div_le_iff₀ hz0).mpr
    nlinarith
  have he : 3 * z / a = (3 / a) * z := by ring
  rw [he, Real.log_mul (by positivity) hz0.ne']
  linarith

theorem initial_gap_rate (r K B₀ B_D z E : ℝ) (m : ℕ)
    (hz : 1 ≤ z) (hr : r ≤ 2 * Real.log z + K)
    (hE : E / 2 ≤ m) (hB : 2 * (K + B₀ + 2) ≤ B_D) :
    Real.exp (r * m - ((B_D + 20 * Real.log z) * m - E) / 2) ≤
      Real.exp (-(B₀ + 1) * m) := by
  apply Real.exp_le_exp.mpr
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log z := Real.log_nonneg hz
  have h₁ := mul_le_mul_of_nonneg_right hr hm0
  have h₂ := mul_le_mul_of_nonneg_right hB hm0
  nlinarith [mul_nonneg hlog hm0]

theorem exp_extra_unit_le_half (B : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    Real.exp (-(B + 1) * m) ≤ Real.exp (-B * m) / 2 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have he : (2 : ℝ) ≤ Real.exp (m : ℝ) := by
    linarith [Real.add_one_le_exp (m : ℝ)]
  have hi : (Real.exp (m : ℝ))⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) he
  calc
    _ = Real.exp (-B * m) * (Real.exp (m : ℝ))⁻¹ := by
      rw [show -(B + 1) * (m : ℝ) = -B * m + -(m : ℝ) by ring, Real.exp_add, Real.exp_neg]
    _ ≤ Real.exp (-B * m) * (2 : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le
    _ = _ := by ring

theorem initial_amplitude_uniform_lower (η : ℂ) (S R B : ℝ) (m : ℕ)
    (hm : 1 ≤ m) (hmain : Real.exp (-B * m) ≤ S)
    (herr : R ≤ Real.exp (-(B + 1) * m)) (hη : S - R ≤ ‖η‖) :
    Real.exp (-(B + 1) * m) ≤ ‖η‖ := by
  have hh := exp_extra_unit_le_half B m hm
  linarith

theorem eventually_bulkCount (z : ℝ) (hz : 0 < z) (F : ℕ → Prop)
    (hF : ∀ᶠ m : ℕ in atTop, F m) :
    ∀ᶠ L : ℝ in atTop, F ⌊z * L⌋₊ := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp hF
  filter_upwards [eventually_ge_atTop ((M : ℝ) / z)] with L hL
  apply hM
  apply Nat.le_floor
  simpa only [mul_comm] using (div_le_iff₀ hz).mp hL

theorem eventually_bulkCount_bounds (z : ℝ) (hz : 0 < z) :
    ∀ᶠ L : ℝ in atTop, 0 < L ∧ 1 ≤ ⌊z * L⌋₊ ∧
      (⌊z * L⌋₊ : ℝ) ≤ z * L ∧ z * L ≤ 2 * ⌊z * L⌋₊ := by
  filter_upwards [eventually_ge_atTop (2 / z)] with L hL
  have h₂ : (2 : ℝ) ≤ z * L := by simpa only [mul_comm] using (div_le_iff₀ hz).mp hL
  have hLp : 0 < L := (div_pos (by norm_num : (0 : ℝ) < 2) hz).trans_le hL
  have hm : 1 ≤ ⌊z * L⌋₊ := (Nat.one_le_floor_iff (z * L)).mpr (by linarith)
  have hm' : (1 : ℝ) ≤ ⌊z * L⌋₊ := by exact_mod_cast hm
  exact ⟨hLp, hm, Nat.floor_le (by positivity), by linarith [Nat.lt_floor_add_one (z * L)]⟩

end Ostmann

end OAI
