import OAI.NumberTheory.Ostmann.Construction.RepeatedTupleEntropy

namespace OAI

/-! # The initial gap absorbs the exact repeated-prime error -/
namespace Ostmann
open Filter

/-- The `L^(2m)` factor is precisely the contribution of the two copies of
all broad positions. Cell normalizers remain in the exponent `A*m`. -/
theorem eventual_initial_repeated_error (r : ℕ) (z K A B Bs B₀ : ℝ)
    (hz : 1 ≤ z) (hBs : 2 * (A + B + 2 * Real.log 4 + B₀ + 3) ≤ Bs) :
    ∀ᶠ m : ℕ in atTop, ∀ L C H Δ : ℝ,
      0 < L → (m : ℝ) ≤ z * L → 0 ≤ C →
      C * L ^ (2 * m) ≤ Real.exp (A * m) → H ≤ B * m →
      (Bs + 8 * Real.log z) * m ≤ Δ →
      K * C * ((2 * (m + r) : ℕ) : ℝ) ^ (2 * (m + r)) * Real.exp (H - Δ / 2) ≤
        Real.exp (-(B₀ + 1) * m) := by
  have hz0 : 0 < z := by linarith
  have hK := ((Real.tendsto_exp_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop K))
  filter_upwards [eventual_repeated_tuple_entropy r z hz0, hK] with m hent hK L C H Δ
    hL hmL hC hnorm hH hΔ
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hden : L ^ (2 * m) ≠ 0 := pow_ne_zero _ hL.ne'
  have hmass : C * ((2 * (m + r) : ℕ) : ℝ) ^ (2 * (m + r)) ≤
      Real.exp (A * m) * Real.exp ((2 * Real.log (4 * z) + 1) * m) := by
    calc
      _ = (C * L ^ (2 * m)) *
          (((2 * (m + r) : ℕ) : ℝ) ^ (2 * (m + r)) / L ^ (2 * m)) := by
        field_simp
      _ ≤ _ := mul_le_mul hnorm (hent L hL hmL) (by positivity) (Real.exp_nonneg _)
  have hgap : H - Δ / 2 ≤ (B - Bs / 2 - 4 * Real.log z) * m := by nlinarith
  have hlogz : 0 ≤ Real.log z := Real.log_nonneg hz
  have hlog4z : Real.log (4 * z) = Real.log 4 + Real.log z :=
    Real.log_mul (by norm_num) hz0.ne'
  calc
    _ = K * (C * ((2 * (m + r) : ℕ) : ℝ) ^ (2 * (m + r))) * Real.exp (H - Δ / 2) := by ring
    _ ≤ Real.exp (m : ℝ) * (Real.exp (A * m) *
          Real.exp ((2 * Real.log (4 * z) + 1) * m)) *
          Real.exp ((B - Bs / 2 - 4 * Real.log z) * m) := by
      apply mul_le_mul
      · exact mul_le_mul hK hmass (by positivity) (Real.exp_nonneg _)
      · exact Real.exp_le_exp.mpr hgap
      · exact Real.exp_nonneg _
      · positivity
    _ = Real.exp (((m : ℝ) + (A * m + (2 * Real.log (4 * z) + 1) * m)) +
        (B - Bs / 2 - 4 * Real.log z) * m) := by simp only [← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [hlog4z]
      have hh := mul_le_mul_of_nonneg_right hBs hm0
      have hl := mul_nonneg hlogz hm0
      nlinarith

end Ostmann

end OAI
