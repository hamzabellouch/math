import OAI.NumberTheory.Ostmann.Characters.TreeComparison

namespace OAI

/-! # A prime-uniform bound for the explicit quartet error -/

namespace Ostmann

private theorem two_bad_error_polynomial_le (C r x t : ℝ)
    (hC : 0 ≤ C) (hC2 : C ≤ 2) (hr1 : r ≤ 1)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    4 * r * C ^ 3 * t + 3 * r * x * C ^ 4 + 4 * x * C ^ 3 +
      (C * t + x * C) ^ 2 * (C ^ 2 * t) ≤ 96 * t + 80 * x := by
  have hc3 : C ^ 3 ≤ (2 : ℝ) ^ 3 := by gcongr
  have hc4 : C ^ 4 ≤ (2 : ℝ) ^ 4 := by gcongr
  have hbase : C * t + x * C ≤ 4 := by
    calc
      _ ≤ (2 : ℝ) * 1 + 1 * 2 := by gcongr
      _ = 4 := by norm_num
  have h1 : 4 * r * C ^ 3 * t ≤ 32 * t := by
    calc
      _ ≤ 4 * 1 * (2 : ℝ) ^ 3 * t := by gcongr
      _ = _ := by ring
  have h2 : 3 * r * x * C ^ 4 ≤ 48 * x := by
    calc
      _ ≤ 3 * 1 * x * (2 : ℝ) ^ 4 := by gcongr
      _ = _ := by ring
  have h3 : 4 * x * C ^ 3 ≤ 32 * x := by
    calc
      _ ≤ 4 * x * (2 : ℝ) ^ 3 := by gcongr
      _ = _ := by ring
  have h4 : (C * t + x * C) ^ 2 * (C ^ 2 * t) ≤ 64 * t := by
    calc
      _ ≤ (4 : ℝ) ^ 2 * (2 ^ 2 * t) := by gcongr
      _ = _ := by ring
  linarith

private theorem local_error_polynomial_le (C r x t s : ℝ)
    (hC : 0 ≤ C) (hC2 : C ≤ 2) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : 0 ≤ s) (hxs : x ≤ s) :
    16 * C ^ 5 * t + 16 * C ^ 3 *
      (2 * C ^ 2 * (t ^ 2 + s) +
        (4 * r * C ^ 3 * t + 3 * r * x * C ^ 4 + 4 * x * C ^ 3 +
          (C * t + x * C) ^ 2 * (C ^ 2 * t))) ≤ 16384 * (t + s) := by
  have hb := two_bad_error_polynomial_le C r x t hC hC2 hr1 hx hx1 ht ht1
  have ht2 : t ^ 2 ≤ t := by nlinarith
  have hf : 2 * C ^ 2 * (t ^ 2 + s) ≤ 8 * (t + s) := by
    calc
      _ ≤ 2 * (2 : ℝ) ^ 2 * (t + s) := by gcongr
      _ = _ := by ring
  have hsum : 2 * C ^ 2 * (t ^ 2 + s) +
      (4 * r * C ^ 3 * t + 3 * r * x * C ^ 4 + 4 * x * C ^ 3 +
        (C * t + x * C) ^ 2 * (C ^ 2 * t)) ≤ 104 * t + 88 * s := by linarith
  calc
    _ ≤ 16 * (2 : ℝ) ^ 5 * t + 16 * 2 ^ 3 * (104 * t + 88 * s) := by gcongr
    _ ≤ _ := by nlinarith

theorem quartetLocalMeanError_le {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    quartetLocalMeanError p ε ≤ 16384 * (ε ^ 2 + Real.sqrt (3 / (p : ℝ))) := by
  let U : ℝ := Fintype.card (ZMod p)ˣ
  let C : ℝ := (p : ℝ) / U
  let r : ℝ := U / p
  let x : ℝ := (p : ℝ)⁻¹
  let t : ℝ := ε ^ 2
  let s : ℝ := Real.sqrt (3 / (p : ℝ))
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hU : U = (p : ℝ) - 1 := by
    dsimp [U]
    rw [ZMod.card_units, Nat.cast_sub (by omega), Nat.cast_one]
  have hU0 : 0 < U := by linarith
  have hC : 0 ≤ C := div_nonneg hp0.le hU0.le
  have hC2 : C ≤ 2 := (div_le_iff₀ hU0).mpr (by linarith)
  have hr : 0 ≤ r := div_nonneg hU0.le hp0.le
  have hr1 : r ≤ 1 := (div_le_iff₀ hp0).mpr (by linarith)
  have hx : 0 ≤ x := inv_nonneg.mpr hp0.le
  have hx1 : x ≤ 1 := by
    dsimp [x]
    exact (inv_le_one₀ hp0).mpr (by linarith)
  have ht : 0 ≤ t := sq_nonneg ε
  have ht1 : t ≤ 1 := by dsimp [t]; nlinarith
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 3 * x := by
    dsimp [s, x]
    rw [Real.sq_sqrt (div_nonneg (by norm_num) hp0.le)]
    rfl
  have hxs : x ≤ s := by nlinarith [sq_nonneg (s - x)]
  have h := local_error_polynomial_le C r x t s hC hC2 hr hr1 hx hx1 ht ht1 hs hxs
  dsimp [C, r, x, t, s] at h
  convert h using 1
  simp only [quartetLocalMeanError, friendlyQuartetError, twoBadQuartetError, U, div_eq_mul_inv]
  ring

end Ostmann

end OAI
