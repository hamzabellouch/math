import Mathlib

namespace OAI
namespace Problem337

/-- A finite iteration estimate for the exceptional-set recurrence.  The
factor `A ^ (1 / (1 - α))` absorbs the geometric sum of exponents. -/
theorem descent_recurrence_bound
    (δ : ℕ → ℝ) (d : ℕ) (ε A α : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hA : 1 ≤ A)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hδ0 : δ 0 = 0) (hδ : ∀ j ≤ d, 0 ≤ δ j)
    (hstep : ∀ j < d, δ (j + 1) ≤ ε + A * (δ j) ^ α) :
    δ d ≤ (d : ℝ) * A ^ (1 / (1 - α)) * ε ^ (α ^ d) := by
  let B : ℝ := A ^ (1 / (1 - α))
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hB1 : 1 ≤ B := Real.one_le_rpow hA (by positivity)
  have hB0 : 0 ≤ B := le_trans zero_le_one hB1
  have hBfixed : A * B ^ α = B := by
    dsimp [B]
    rw [← Real.rpow_mul hA0]
    calc
      A * A ^ (1 / (1 - α) * α) = A ^ (1 + 1 / (1 - α) * α) := by
        rw [Real.rpow_add hApos, Real.rpow_one]
      _ = A ^ (1 / (1 - α)) := by
        congr 1
        field_simp [show 1 - α ≠ 0 by linarith]
        ring
  have hbound : ∀ j ≤ d, δ j ≤ (j : ℝ) * B * ε ^ (α ^ j) := by
    intro j
    induction j with
    | zero =>
      intro _
      simp [hδ0]
    | succ j ih =>
      intro hj
      have hjd : j ≤ d := by omega
      have hjlt : j < d := by omega
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hpowε : 0 ≤ ε ^ (α ^ (j + 1)) := Real.rpow_nonneg hε0 _
      have hεsmall : ε ≤ ε ^ (α ^ (j + 1)) := by
        simpa using Real.rpow_le_rpow_of_exponent_ge' hε0 hε1
          (pow_nonneg hα0.le _) (pow_le_one₀ hα0.le hα1.le)
      have hjpow : (j : ℝ) ^ α ≤ j := by
        cases j with
        | zero => simp [Real.zero_rpow hα0.ne']
        | succ j =>
          exact Real.rpow_le_self_of_one_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)) hα1.le
      have hpower : ((j : ℝ) * B * ε ^ (α ^ j)) ^ α =
          (j : ℝ) ^ α * B ^ α * ε ^ (α ^ (j + 1)) := by
        rw [Real.mul_rpow (mul_nonneg hj0 hB0) (Real.rpow_nonneg hε0 _),
          Real.mul_rpow hj0 hB0, ← Real.rpow_mul hε0, pow_succ]
      calc
        δ (j + 1) ≤ ε + A * (δ j) ^ α := hstep j hjlt
        _ ≤ ε + A * ((j : ℝ) * B * ε ^ (α ^ j)) ^ α := by
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (hδ j hjd) (ih hjd) hα0.le) hA0)
        _ = ε + (j : ℝ) ^ α * B * ε ^ (α ^ (j + 1)) := by
          rw [hpower]
          calc
            ε + A * ((j : ℝ) ^ α * B ^ α * ε ^ (α ^ (j + 1))) =
                ε + (j : ℝ) ^ α * (A * B ^ α) * ε ^ (α ^ (j + 1)) := by ring
            _ = _ := by rw [hBfixed]
        _ ≤ ε ^ (α ^ (j + 1)) + (j : ℝ) * B * ε ^ (α ^ (j + 1)) := by
          exact add_le_add hεsmall
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hjpow hB0) hpowε)
        _ ≤ (j + 1 : ℕ) * B * ε ^ (α ^ (j + 1)) := by
          push_cast
          nlinarith [mul_le_mul_of_nonneg_right hB1 hpowε]
  exact hbound d le_rfl

/-- The same estimate with the direction of indexing used by the backwards
construction of good numerator sets. -/
theorem descent_recurrence_bound_backward
    (δ : ℕ → ℝ) (d : ℕ) (ε A α : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hA : 1 ≤ A)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hδd : δ d = 0) (hδ : ∀ j ≤ d, 0 ≤ δ j)
    (hstep : ∀ j < d, δ j ≤ ε + A * (δ (j + 1)) ^ α) :
    δ 0 ≤ (d : ℝ) * A ^ (1 / (1 - α)) * ε ^ (α ^ d) := by
  have h := descent_recurrence_bound (fun j => δ (d - j)) d ε A α
    hε0 hε1 hA hα0 hα1 (by simpa using hδd)
    (fun j _ => hδ (d - j) (Nat.sub_le d j)) (by
      intro j hj
      have ht : d - (j + 1) < d := by omega
      have heq : d - (j + 1) + 1 = d - j := by omega
      simpa only [heq] using hstep (d - (j + 1)) ht)
  simpa using h

/-- Exponential form of the finite exceptional-density estimate. -/
theorem descent_recurrence_exp_bound
    (δ : ℕ → ℝ) (d : ℕ) (a b α : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hα0 : 0 < α) (hα1 : α < 1)
    (hδd : δ d = 0) (hδ : ∀ j ≤ d, 0 ≤ δ j)
    (hstep : ∀ j < d,
      δ j ≤ Real.exp (-b) + Real.exp a * (δ (j + 1)) ^ α) :
    δ 0 ≤ (d : ℝ) * Real.exp (a / (1 - α) - b * α ^ d) := by
  have h := descent_recurrence_bound_backward δ d (Real.exp (-b)) (Real.exp a) α
    (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith))
    (Real.one_le_exp_iff.mpr ha) hα0 hα1 hδd hδ hstep
  calc
    δ 0 ≤ (d : ℝ) * (Real.exp a) ^ (1 / (1 - α)) *
        (Real.exp (-b)) ^ (α ^ d) := h
    _ = (d : ℝ) * Real.exp (a / (1 - α) - b * α ^ d) := by
      rw [← Real.exp_mul, ← Real.exp_mul, mul_assoc, ← Real.exp_add]
      congr 2
      ring

end Problem337

end OAI
