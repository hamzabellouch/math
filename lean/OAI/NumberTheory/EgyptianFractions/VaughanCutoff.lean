import Mathlib

namespace OAI
noncomputable section
open Filter

namespace Problem337.Vaughan

/-- The conventional balanced natural cutoff for Vaughan's identity. -/
def optimizedCutoff (X : ℝ) : ℕ := ⌊X ^ (2 / 5 : ℝ)⌋₊

theorem optimizedCutoff_le (X : ℝ) (hX : 0 ≤ X) :
    (optimizedCutoff X : ℝ) ≤ X ^ (2 / 5 : ℝ) :=
  Nat.floor_le (Real.rpow_nonneg hX _)

theorem optimizedCutoff_lower (X : ℝ) (hX : 2 ≤ X ^ (2 / 5 : ℝ)) :
    X ^ (2 / 5 : ℝ) / 2 ≤ (optimizedCutoff X : ℝ) := by
  have hfloor := Nat.lt_floor_add_one (X ^ (2 / 5 : ℝ))
  unfold optimizedCutoff
  linarith

theorem optimizedCutoff_pos (X : ℝ) (hX : 2 ≤ X ^ (2 / 5 : ℝ)) :
    0 < optimizedCutoff X := by
  have h : 2 ≤ optimizedCutoff X := Nat.le_floor hX
  omega

theorem optimizedCutoff_sq_le (X : ℝ) (hX : 0 ≤ X) :
    (optimizedCutoff X : ℝ) ^ 2 ≤ X ^ (4 / 5 : ℝ) := by
  have hpow : (X ^ (2 / 5 : ℝ)) ^ 2 = X ^ (4 / 5 : ℝ) := by
    have h := Real.rpow_mul hX (2 / 5 : ℝ) (2 : ℝ)
    norm_num at h
    exact h.symm
  rw [← hpow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (optimizedCutoff_le X hX) 2

theorem optimizedCutoff_le_four_fifths (X : ℝ) (hX : 1 ≤ X) :
    (optimizedCutoff X : ℝ) ≤ X ^ (4 / 5 : ℝ) :=
  (optimizedCutoff_le X (by linarith)).trans
    (Real.rpow_le_rpow_of_exponent_le hX (by norm_num))

/-- The reciprocal square-root loss from a long-variable cutoff has precisely
the required four-fifths power, with a harmless explicit constant. -/
theorem div_sqrt_optimizedCutoff_le (X : ℝ) (hX : 0 < X)
    (hpow : 2 ≤ X ^ (2 / 5 : ℝ)) :
    X / Real.sqrt (optimizedCutoff X : ℝ) ≤ 2 * X ^ (4 / 5 : ℝ) := by
  have hsq : (X ^ (1 / 5 : ℝ)) ^ 2 = X ^ (2 / 5 : ℝ) := by
    have h := Real.rpow_mul hX.le (1 / 5 : ℝ) (2 : ℝ)
    norm_num at h
    exact h.symm
  have hcut := optimizedCutoff_lower X hpow
  have hs : X ^ (1 / 5 : ℝ) / 2 ≤ Real.sqrt (optimizedCutoff X : ℝ) := by
    apply (Real.le_sqrt (by positivity) (Nat.cast_nonneg _)).mpr
    nlinarith [sq_nonneg (X ^ (1 / 5 : ℝ))]
  have hpos : 0 < Real.sqrt (optimizedCutoff X : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast optimizedCutoff_pos X hpow)
  apply (div_le_iff₀ hpos).mpr
  have hprod : X ^ (4 / 5 : ℝ) * X ^ (1 / 5 : ℝ) = X := by
    rw [← Real.rpow_add hX]
    norm_num
  calc
    X = X ^ (4 / 5 : ℝ) * X ^ (1 / 5 : ℝ) := hprod.symm
    _ = (2 * X ^ (4 / 5 : ℝ)) * (X ^ (1 / 5 : ℝ) / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

/-- A concrete scalar optimization of the cutoff-dependent error terms. -/
theorem optimizedCutoff_error_le (X : ℝ) (hX : 1 ≤ X)
    (hpow : 2 ≤ X ^ (2 / 5 : ℝ)) :
    (optimizedCutoff X : ℝ) + (optimizedCutoff X : ℝ) ^ 2 +
        X / Real.sqrt (optimizedCutoff X : ℝ) ≤ 4 * X ^ (4 / 5 : ℝ) := by
  have h1 := optimizedCutoff_le_four_fifths X hX
  have h2 := optimizedCutoff_sq_le X (by linarith)
  have h3 := div_sqrt_optimizedCutoff_le X (by linarith) hpow
  linarith

/-- The short initial segment is also absorbed by the four-fifths budget. -/
theorem optimizedCutoff_log_le (X : ℝ) (hX : 1 ≤ X)
    (hpow : 2 ≤ X ^ (2 / 5 : ℝ)) :
    (optimizedCutoff X : ℝ) * Real.log (optimizedCutoff X : ℝ) ≤
      X ^ (4 / 5 : ℝ) * Real.log X := by
  have hUX : (optimizedCutoff X : ℝ) ≤ X := by
    calc
      _ ≤ X ^ (2 / 5 : ℝ) := optimizedCutoff_le X (by linarith)
      _ ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
      _ = X := Real.rpow_one X
  have hlog : Real.log (optimizedCutoff X : ℝ) ≤ Real.log X :=
    Real.log_le_log (by exact_mod_cast optimizedCutoff_pos X hpow) hUX
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  exact (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)).trans
    (mul_le_mul_of_nonneg_right (optimizedCutoff_le_four_fifths X hX) hlogX)

/-- Scalar normalization to the usual three-term Vaughan envelope. The
Diophantine denominator only needs the ordinary range `1 ≤ q ≤ X`. -/
theorem optimizedCutoff_standard_envelope (X q : ℝ) (hX : 1 ≤ X)
    (hq : 1 ≤ q) (hqX : q ≤ X) (hpow : 2 ≤ X ^ (2 / 5 : ℝ)) :
    X / q + ((optimizedCutoff X : ℝ) + (optimizedCutoff X : ℝ) ^ 2 +
        X / Real.sqrt (optimizedCutoff X : ℝ)) + q ≤
      4 * (X / Real.sqrt q + X ^ (4 / 5 : ℝ) + Real.sqrt (X * q)) := by
  have hX0 : 0 ≤ X := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hsqpos : 0 < Real.sqrt q := Real.sqrt_pos.mpr (by linarith)
  have hsqq : Real.sqrt q ≤ q := Real.sqrt_le_self_iff.mpr (Or.inr hq)
  have hdiv : X / q ≤ X / Real.sqrt q :=
    div_le_div_of_nonneg_left hX0 hsqpos hsqq
  have hqsqrt : q ≤ Real.sqrt (X * q) := by
    apply (Real.le_sqrt hq0 (mul_nonneg hX0 hq0)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hqX hq0]
  have herr := optimizedCutoff_error_le X hX hpow
  have hnonneg : 0 ≤ X / Real.sqrt q := div_nonneg hX0 hsqpos.le
  nlinarith [Real.sqrt_nonneg (X * q)]

/-- Optimization of the square-root expression arising from a Type II block.
Both long-variable cutoffs are the same balanced natural cutoff. -/
theorem sqrt_optimizedCutoff_envelope_le (X q : ℝ) (hX : 1 ≤ X)
    (hq : 0 < q) (hpow : 2 ≤ X ^ (2 / 5 : ℝ)) :
    Real.sqrt (X * (X / q + X / (optimizedCutoff X : ℝ) +
        X / (optimizedCutoff X : ℝ) + q)) ≤
      3 * (X / Real.sqrt q + X ^ (4 / 5 : ℝ) + Real.sqrt (X * q)) := by
  have hX0 : 0 ≤ X := by linarith
  have hU0 : 0 < (optimizedCutoff X : ℝ) := by
    exact_mod_cast optimizedCutoff_pos X hpow
  have hA : 0 ≤ X / Real.sqrt q := by positivity
  have hB : 0 ≤ X ^ (4 / 5 : ℝ) := by positivity
  have hC : 0 ≤ Real.sqrt (X * q) := Real.sqrt_nonneg _
  have hqeq : X * (X / q) = (X / Real.sqrt q) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hq.le]
    ring
  have hUeq : X * (X / (optimizedCutoff X : ℝ)) =
      (X / Real.sqrt (optimizedCutoff X : ℝ)) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hU0.le]
    ring
  have hUbound := pow_le_pow_left₀ (show 0 ≤ X / Real.sqrt (optimizedCutoff X : ℝ) by
    positivity) (div_sqrt_optimizedCutoff_le X (by linarith) hpow) 2
  have hCeq := Real.sq_sqrt (mul_nonneg hX0 hq.le)
  apply (Real.sqrt_le_left (by positivity)).mpr
  rw [mul_add, mul_add, mul_add, hqeq, hUeq]
  nlinarith [mul_nonneg hA hB, mul_nonneg hA hC, mul_nonneg hB hC,
    sq_nonneg (X / Real.sqrt q), sq_nonneg (X ^ (4 / 5 : ℝ)),
    sq_nonneg (Real.sqrt (X * q))]

/-- The precise squared Type II block budget transfers to the standard
Vaughan envelope after choosing both cutoffs as `optimizedCutoff X`. -/
theorem optimizedCutoff_squared_budget (X q C R : ℝ) (hX : 1 ≤ X)
    (hq : 0 < q) (hC : 0 ≤ C) (hpow : 2 ≤ X ^ (2 / 5 : ℝ))
    (hbound : R ^ 2 ≤ C * X * (1 + Real.log (2 * X)) ^ 6 *
      (X / q + X / (optimizedCutoff X : ℝ) + X / (optimizedCutoff X : ℝ) + q)) :
    R ≤ 3 * Real.sqrt C * (1 + Real.log (2 * X)) ^ 3 *
      (X / Real.sqrt q + X ^ (4 / 5 : ℝ) + Real.sqrt (X * q)) := by
  let L : ℝ := 1 + Real.log (2 * X)
  let E : ℝ := X / Real.sqrt q + X ^ (4 / 5 : ℝ) + Real.sqrt (X * q)
  have hX0 : 0 ≤ X := by linarith
  have hL : 0 ≤ L := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * X by linarith)
    dsimp [L]
    linarith
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hD : X * (X / q + X / (optimizedCutoff X : ℝ) +
      X / (optimizedCutoff X : ℝ) + q) ≤ (3 * E) ^ 2 :=
    (Real.sqrt_le_left (by positivity)).mp (sqrt_optimizedCutoff_envelope_le X q hX hq hpow)
  change R ≤ 3 * Real.sqrt C * L ^ 3 * E
  apply le_of_sq_le_sq _ (by positivity)
  calc
    R ^ 2 ≤ C * X * L ^ 6 *
        (X / q + X / (optimizedCutoff X : ℝ) + X / (optimizedCutoff X : ℝ) + q) := hbound
    _ = (C * L ^ 6) * (X *
        (X / q + X / (optimizedCutoff X : ℝ) + X / (optimizedCutoff X : ℝ) + q)) := by ring
    _ ≤ (C * L ^ 6) * (3 * E) ^ 2 := mul_le_mul_of_nonneg_left hD (by positivity)
    _ = (3 * Real.sqrt C * L ^ 3 * E) ^ 2 := by
      have hs := Real.sq_sqrt hC
      calc
        _ = (3 * E) ^ 2 * L ^ 6 * (Real.sqrt C) ^ 2 := by rw [hs]; ring
        _ = _ := by ring

/-- All cutoff inequalities hold simultaneously beyond one real threshold. -/
theorem eventually_optimizedCutoff_bounds :
    ∀ᶠ X : ℝ in atTop,
      0 < optimizedCutoff X ∧
      X ^ (2 / 5 : ℝ) / 2 ≤ (optimizedCutoff X : ℝ) ∧
      (optimizedCutoff X : ℝ) ≤ X ^ (2 / 5 : ℝ) ∧
      (optimizedCutoff X : ℝ) ^ 2 ≤ X ^ (4 / 5 : ℝ) ∧
      X / Real.sqrt (optimizedCutoff X : ℝ) ≤ 2 * X ^ (4 / 5 : ℝ) := by
  have hlarge := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 5)).eventually
    (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℝ)] with X hpow hX
  exact ⟨optimizedCutoff_pos X hpow, optimizedCutoff_lower X hpow,
    optimizedCutoff_le X (by linarith), optimizedCutoff_sq_le X (by linarith),
    div_sqrt_optimizedCutoff_le X (by linarith) hpow⟩

end Problem337.Vaughan

end

end OAI
