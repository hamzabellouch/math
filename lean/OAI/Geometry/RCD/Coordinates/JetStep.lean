import OAI.Geometry.RCD.Coordinates.FactorialMajorant

namespace OAI

/-!
# Scalar all-order jet step

At Gevrey exponent `σ = 2`, the factorial weights in an increment leave
only the factor `(m + 1)^3` relative to the allowed jet size.  The next
dyadic scale contributes `2 / 2^m`.  A single small parameter controls
every order `m ≥ 2`.  The differential estimates producing the old jet
and increment are explicit premises of the scalar theorem below.
-/

namespace RegularPointCoordinates

noncomputable section

/-- The polynomial growth is dominated by the dyadic factor, including
the largest case at order three. -/
theorem cubic_le_eight_mul_two_pow (m : ℕ) :
    ((m : ℝ) + 1) ^ 3 ≤ 8 * (2 : ℝ) ^ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m ≤ 3
    · interval_cases m <;> norm_num
    have hm4 : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 4 ≤ m)
    have hmone : 1 ≤ m := by omega
    have hprev : (m : ℝ) ^ 3 ≤ 8 * (2 : ℝ) ^ (m - 1) := by
      have h := ih (m - 1) (by omega)
      have hcast : ((m - 1 : ℕ) : ℝ) + 1 = m := by
        exact_mod_cast (Nat.sub_add_cancel hmone)
      simpa only [hcast] using h
    have hfactor : (0 : ℝ) ≤ ((m : ℝ) - 4) * ((m : ℝ) ^ 2 + m + 1) :=
      mul_nonneg (sub_nonneg.mpr hm4) (by positivity)
    have hstep : ((m : ℝ) + 1) ^ 3 ≤ 2 * (m : ℝ) ^ 3 := by
      nlinarith only [hfactor]
    have hpow : (2 : ℝ) ^ m = 2 * (2 : ℝ) ^ (m - 1) := by
      calc
        _ = (2 : ℝ) ^ ((m - 1) + 1) := by rw [Nat.sub_add_cancel hmone]
        _ = _ := by rw [pow_succ]; ring
    calc
      _ ≤ 2 * (m : ℝ) ^ 3 := hstep
      _ ≤ 2 * (8 * (2 : ℝ) ^ (m - 1)) := mul_le_mul_of_nonneg_left hprev (by norm_num)
      _ = _ := by rw [hpow]; ring

theorem dyadic_cubic_le_sixteen (m : ℕ) :
    (2 / (2 : ℝ) ^ m) * ((m : ℝ) + 1) ^ 3 ≤ 16 := by
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ m)]
  nlinarith only [cubic_le_eight_mul_two_pow m]

theorem dyadic_jet_factor_le_half {m : ℕ} (hm : 2 ≤ m) :
    2 / (2 : ℝ) ^ m ≤ 1 / 2 := by
  have hpow : (4 : ℝ) ≤ (2 : ℝ) ^ m := by
    convert pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm using 1
    norm_num
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ m)).mpr
  nlinarith

/-- Cancellation of factorials and the old exponential base. -/
theorem jet_increment_factorization {B : ℝ} {m : ℕ} (hm : 1 ≤ m) :
    B ^ m * factorialMajorant m * (m.factorial : ℝ) =
      (B * ((m : ℝ) + 1) ^ 3) *
        (B ^ (m - 1) * (m.factorial : ℝ) ^ 3) := by
  have hpow : B ^ m = B ^ (m - 1) * B := by
    calc
      _ = B ^ ((m - 1) + 1) := by rw [Nat.sub_add_cancel hm]
      _ = _ := by rw [pow_succ]
  rw [hpow]
  unfold factorialMajorant
  rw [Nat.factorial_succ]
  push_cast
  ring

/-- The all-order scalar jet step with an explicit smallness condition. -/
theorem scalar_jet_step {B C epsilon old increment : ℝ} {m : ℕ}
    (hB : 0 ≤ B) (hm : 2 ≤ m) (hsmall : epsilon * C * B ≤ 1 / 32)
    (hold : old ≤ B ^ (m - 1) * (m.factorial : ℝ) ^ 3)
    (hincrement : increment ≤ epsilon * C * B ^ m *
      factorialMajorant m * (m.factorial : ℝ)) :
    (2 / (2 : ℝ) ^ m) * (old + increment) ≤
      B ^ (m - 1) * (m.factorial : ℝ) ^ 3 := by
  let allowance := B ^ (m - 1) * (m.factorial : ℝ) ^ 3
  have hallowance : 0 ≤ allowance := by dsimp [allowance]; positivity
  have hincrement' : increment ≤
      (epsilon * C * B * ((m : ℝ) + 1) ^ 3) * allowance := by
    calc
      _ ≤ epsilon * C * B ^ m * factorialMajorant m * (m.factorial : ℝ) := hincrement
      _ = _ := by
        have h := jet_increment_factorization (B := B) (m := m) (by omega)
        dsimp [allowance]
        calc
          _ = (epsilon * C) * (B ^ m * factorialMajorant m * (m.factorial : ℝ)) := by ring
          _ = _ := by rw [h]; ring
  have hproduct : epsilon * C * B *
      ((2 / (2 : ℝ) ^ m) * ((m : ℝ) + 1) ^ 3) ≤ 1 / 2 := by
    have h := mul_le_mul hsmall (dyadic_cubic_le_sixteen m)
      (by positivity : (0 : ℝ) ≤ (2 / (2 : ℝ) ^ m) * ((m : ℝ) + 1) ^ 3)
      (by norm_num : (0 : ℝ) ≤ 1 / 32)
    norm_num at h ⊢
    exact h
  have hcoefficient : 2 / (2 : ℝ) ^ m + epsilon * C * B *
      ((2 / (2 : ℝ) ^ m) * ((m : ℝ) + 1) ^ 3) ≤ 1 := by
    linarith [dyadic_jet_factor_le_half hm]
  calc
    _ ≤ (2 / (2 : ℝ) ^ m) *
        (allowance + (epsilon * C * B * ((m : ℝ) + 1) ^ 3) * allowance) :=
      mul_le_mul_of_nonneg_left (add_le_add hold hincrement') (by positivity)
    _ = (2 / (2 : ℝ) ^ m + epsilon * C * B *
        ((2 / (2 : ℝ) ^ m) * ((m : ℝ) + 1) ^ 3)) * allowance := by ring
    _ ≤ 1 * allowance := mul_le_mul_of_nonneg_right hcoefficient hallowance
    _ = _ := by simp [allowance]

/-- A positive parameter can be fixed once, after fixing the constants,
so that the scalar jet step holds at every positive order above one. -/
theorem exists_uniform_scalar_jet_step {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ (m : ℕ) (old increment : ℝ), 2 ≤ m →
      old ≤ B ^ (m - 1) * (m.factorial : ℝ) ^ 3 →
      increment ≤ epsilon * C * B ^ m * factorialMajorant m * (m.factorial : ℝ) →
      (2 / (2 : ℝ) ^ m) * (old + increment) ≤
        B ^ (m - 1) * (m.factorial : ℝ) ^ 3 := by
  let epsilon := 1 / (32 * (C * B + 1))
  have hCB : 0 ≤ C * B := mul_nonneg hC hB
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hsmall : epsilon * C * B ≤ 1 / 32 := by
    have hden : 0 < 32 * (C * B + 1) := by positivity
    calc
      _ = (C * B) / (32 * (C * B + 1)) := by dsimp [epsilon]; ring
      _ ≤ 1 / 32 := (div_le_iff₀ hden).mpr (by nlinarith)
  exact ⟨epsilon, hepsilon, fun m old increment hm hold hincrement =>
    scalar_jet_step hB hm hsmall hold hincrement⟩

end

end RegularPointCoordinates

end OAI
