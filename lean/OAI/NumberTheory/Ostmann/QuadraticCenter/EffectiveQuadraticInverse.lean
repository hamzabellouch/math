import OAI.NumberTheory.Ostmann.Quadratic.QuadraticInverse

namespace OAI

/-! # Choosing the actual approximation cutoff for the inverse quadratic step -/

namespace Ostmann

open scoped BigOperators

/-- A quadratic sum of relative squared size ρ has a small denominator,
with the expected N⁻² precision up to a logarithmic factor. -/
theorem effective_quadratic_inverse (α β ρ : ℝ) (N : ℕ)
    (hN : 0 < N) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hscale : 512 * (1 + 2 * Real.log (N : ℝ)) ≤ ρ * N)
    (hlarge : ρ * (N : ℝ) ^ 2 ≤
      ‖∑ j ∈ Finset.range N, realQuadraticPhase α β j‖ ^ 2) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ 1024 / ρ ∧
      |(q : ℝ) * α - (round ((q : ℝ) * α) : ℤ)| ≤
        1024 * (1 + 2 * Real.log (N : ℝ)) / (ρ * (N : ℝ) ^ 2) := by
  let B := 1 + 2 * Real.log (N : ℝ)
  let R := ρ * (N : ℝ) ^ 2 / (1024 * B)
  let Q : ℕ := ⌊R⌋₊
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hBp : 0 < B := by linarith
  have hN512 : (512 : ℝ) ≤ N := by
    have hm := mul_le_mul_of_nonneg_right hρ1 hNp.le
    dsimp [B] at hB
    linarith
  have hR1 : 1 ≤ R := by
    apply (le_div_iff₀ (show 0 < 1024 * B by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_right hscale hNp.le
    have hb : 0 ≤ B * ((N : ℝ) - 2) :=
      mul_nonneg hBp.le (by linarith)
    dsimp [B] at hb ⊢
    nlinarith
  have hQ : 0 < Q := by
    have hh : 1 ≤ Q := Nat.le_floor (by simpa only [Nat.cast_one] using hR1)
    omega
  have hQle : (Q : ℝ) ≤ R := Nat.floor_le (by positivity)
  have hRle : R ≤ (N : ℝ) ^ 2 := by
    apply (div_le_iff₀ (show 0 < 1024 * B by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_right hρ1 (sq_nonneg (N : ℝ))
    have hb := mul_le_mul_of_nonneg_right hB (sq_nonneg (N : ℝ))
    nlinarith
  have hQp : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hlogQ : 1 + Real.log (Q : ℝ) ≤ B := by
    have hh := Real.log_le_log hQp (hQle.trans hRle)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    dsimp [B]
    linarith
  have hQR : 512 * (Q : ℝ) * B ≤ ρ * (N : ℝ) ^ 2 := by
    have hh := (le_div_iff₀ (show 0 < 1024 * B by positivity)).mp hQle
    nlinarith
  obtain ⟨q, hq, hqsize, hqapprox⟩ := quadratic_inverse_approximation α β ρ B N Q
    hN hQ hρ hB hlogQ hscale hQR hlarge
  refine ⟨q, hq, hqsize, hqapprox.trans ?_⟩
  have hRupper : R ≤ (Q : ℝ) + 1 := (Nat.lt_floor_add_one R).le
  have hRp : 0 < R := by positivity
  calc
    1 / ((Q : ℝ) + 1) ≤ 1 / R := one_div_le_one_div_of_le hRp hRupper
    _ = _ := by dsimp [R, B]; field_simp

end Ostmann

end OAI
