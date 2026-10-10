import OAI.NumberTheory.Ostmann.Quadratic.CommonCenterScale

namespace OAI

/-! # Integer cutoffs for the original rational-center extraction -/

namespace Ostmann

theorem commonCenter_original_cutoffs (T X : ℝ) (r : ℕ) (hT : 1 ≤ T) (hX : 1 ≤ X)
    (hXU : X ≤ Real.exp ((r - 10 : ℕ) * T)) :
    0 < ⌈Real.exp (13 * T / 100)⌉₊ ∧
    (⌈Real.exp (13 * T / 100)⌉₊ : ℝ) ≤ 2 * Real.exp (T / 5) ∧
    (⌈X * Real.exp (13 * T / 100)⌉₊ : ℝ) ≤
      2 * Real.exp ((r - 10 : ℕ) * T + T / 5) ∧
    0 < ⌊Real.exp T⌋₊ ∧ Real.exp T / 2 ≤ (⌊Real.exp T⌋₊ : ℝ) := by
  have hT0 : 0 ≤ T := by linarith
  have hE : 1 ≤ Real.exp (13 * T / 100) := Real.one_le_exp (by positivity)
  have hE' : Real.exp (13 * T / 100) ≤ Real.exp (T / 5) :=
    Real.exp_le_exp.mpr (by linarith)
  have hA : (⌈Real.exp (13 * T / 100)⌉₊ : ℝ) ≤ 2 * Real.exp (T / 5) := by
    have hh := Nat.ceil_lt_add_one (Real.exp_nonneg (13 * T / 100))
    linarith
  have hXE : 0 ≤ X * Real.exp (13 * T / 100) := by positivity
  have hH : (⌈X * Real.exp (13 * T / 100)⌉₊ : ℝ) ≤
      2 * Real.exp ((r - 10 : ℕ) * T + T / 5) := by
    have hh := Nat.ceil_lt_add_one hXE
    have hbound : X * Real.exp (13 * T / 100) ≤ Real.exp ((r - 10 : ℕ) * T + T / 5) := by
      rw [Real.exp_add]
      exact mul_le_mul hXU hE' (Real.exp_nonneg _) (Real.exp_nonneg _)
    have h1 : 1 ≤ X * Real.exp (13 * T / 100) := by nlinarith
    linarith
  have h2 : (2 : ℝ) ≤ Real.exp T := by linarith [Real.add_one_le_exp T]
  have hfloor := Nat.lt_floor_add_one (Real.exp T)
  have hfloorpos : 0 < ⌊Real.exp T⌋₊ := by
    have hh : (1 : ℝ) ≤ ⌊Real.exp T⌋₊ := by linarith
    exact_mod_cast hh
  exact ⟨Nat.ceil_pos.mpr (Real.exp_pos _), hA, hH, hfloorpos, by linarith⟩

end Ostmann

end OAI
