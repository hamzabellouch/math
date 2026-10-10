import OAI.NumberTheory.Ostmann.Arithmetic.VariableModulusSupport

namespace OAI

/-! # The numerical rate after the actual arithmetic frequency sum -/

namespace Ostmann
open Filter

/-- The divisor constant is chosen uniformly before the history-dependent
modulus. This is the numerical estimate used by the same-assignment norm. -/
theorem arithmetic_frequency_budget_rate (n : ℕ) (K C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∃ D : ℝ, 0 ≤ D ∧
      (∀ q : ℕ, q ≠ 0 → (q : ℝ) ≤ Real.exp (2 * C * m) → (q.divisors.card : ℝ) ≤ D) ∧
      ∀ N V : ℕ, ∀ Δ : ℝ, (N : ℝ) ≤ Real.exp (C * m) →
      (V : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      Real.exp (-(2 ^ n : ℕ) * Δ + K) *
        ((8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) *
          (2 * (V : ℝ)) ^ (2 * 2 ^ n)) ≤
        Real.exp ((2 ^ n : ℕ) * Δ + ε * m) := by
  let r : ℕ := 2 ^ n
  have hr : (0 : ℝ) < r := by exact_mod_cast (Nat.two_pow_pos n)
  let δ : ℝ := ε / (2 * r)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδr : δ * r = ε / 2 := by dsimp [δ]; field_simp
  obtain ⟨M, hM⟩ := leaf_frequency_budget_sublinear r K (ε / 8) (by positivity)
  filter_upwards [frequency_budget_subexponential C δ hC hδ,
    eventually_ge_atTop (M / 4), eventually_ge_atTop (0 : ℝ)] with m hrate hm hm0
  obtain ⟨D, hD, hdiv, hcost⟩ := hrate
  refine ⟨D, hD, hdiv, ?_⟩
  intro N V Δ hN hV
  have hC0 : 0 ≤ 8 * D ^ 4 * (1 + Real.log N) ^ 3 := by
    have := Real.log_natCast_nonneg N
    positivity
  have hnode : (8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (r - 1) ≤
      Real.exp ((ε / 2) * m) := by
    calc
      _ ≤ Real.exp (δ * m) ^ (r - 1) := pow_le_pow_left₀ hC0 (hcost N hN) _
      _ = Real.exp ((r - 1 : ℕ) * (δ * m)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hcount : ((r - 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le r 1
        have h := mul_le_mul_of_nonneg_right hcount (mul_nonneg hδ.le hm0)
        nlinarith [hδr]
  have hleaf : (2 * (V : ℝ)) ^ (2 * r) * Real.exp (-(r : ℝ) * Δ + K) ≤
      Real.exp ((r : ℝ) * Δ + (ε / 2) * m) := by
    convert hM (4 * m) (by linarith) Δ V hV using 1
    congr 1
    ring
  calc
    _ = (8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (r - 1) *
        ((2 * (V : ℝ)) ^ (2 * r) * Real.exp (-(r : ℝ) * Δ + K)) := by ring
    _ ≤ Real.exp ((ε / 2) * m) * Real.exp ((r : ℝ) * Δ + (ε / 2) * m) :=
      mul_le_mul hnode hleaf (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; dsimp [r]; congr 1; ring

/-- There are `r*m` bulk Page factors and `m` spectators. Their combined
loss is exactly `2 * 6^(r*m)`, independently of the depth. -/
theorem arithmetic_norm_page_spectator_cost (n m : ℕ) :
    (2 : ℝ) ^ (2 ^ n * m) * 2 * 3 ^ (2 ^ n * m) =
      2 * Real.exp (Real.log 6 * (2 ^ n : ℕ) * m) := by
  rw [mul_right_comm _ 2, ← mul_pow, show (2 : ℝ) * 3 = 6 by norm_num, mul_comm _ 2]
  congr 1
  rw [show Real.log 6 * (2 ^ n : ℕ) * m = ((2 ^ n * m : ℕ) : ℝ) * Real.log 6 by
    push_cast
    ring, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 6)]

/-- Fixed profile constants are absorbed without changing the coefficient
`log 6` of the bulk cost. -/
theorem arithmetic_norm_budget_rate (n : ℕ) (A C ε : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∃ D : ℝ, 0 ≤ D ∧
      (∀ q : ℕ, q ≠ 0 → (q : ℝ) ≤ Real.exp (2 * C * m) → (q.divisors.card : ℝ) ≤ D) ∧
      ∀ N V : ℕ, ∀ Δ : ℝ, (N : ℝ) ≤ Real.exp (C * m) →
      (V : ℝ) ≤ Real.exp (Δ + Real.sqrt (4 * m)) →
      (A * Real.exp (-(2 ^ n : ℕ) * Δ)) *
        ((2 * Real.exp (Real.log 6 * (2 ^ n : ℕ) * m)) *
          ((8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) *
            (2 * (V : ℝ)) ^ (2 * 2 ^ n))) ≤
        Real.exp ((2 ^ n : ℕ) * Δ + Real.log 6 * (2 ^ n : ℕ) * m + ε * m) := by
  let K := Real.log (2 * A + 1)
  have hK : 2 * A ≤ Real.exp K := by
    dsimp only [K]
    rw [Real.exp_log (by positivity : 0 < 2 * A + 1)]
    linarith
  filter_upwards [arithmetic_frequency_budget_rate n K C ε hC hε] with m hm
  obtain ⟨D, hD, hdiv, hcost⟩ := hm
  refine ⟨D, hD, hdiv, ?_⟩
  intro N V Δ hN hV
  have hb : 0 ≤ (8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) *
      (2 * (V : ℝ)) ^ (2 * 2 ^ n) := by
    have := Real.log_natCast_nonneg N
    positivity
  calc
    _ = Real.exp (Real.log 6 * (2 ^ n : ℕ) * m) *
        ((2 * A) * Real.exp (-(2 ^ n : ℕ) * Δ) *
          ((8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) *
            (2 * (V : ℝ)) ^ (2 * 2 ^ n))) := by ring
    _ ≤ Real.exp (Real.log 6 * (2 ^ n : ℕ) * m) *
        (Real.exp (-(2 ^ n : ℕ) * Δ + K) *
          ((8 * D ^ 4 * (1 + Real.log N) ^ 3) ^ (2 ^ n - 1) *
            (2 * (V : ℝ)) ^ (2 * 2 ^ n))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le).trans_eq (mul_comm _ _)) hb
    _ ≤ Real.exp (Real.log 6 * (2 ^ n : ℕ) * m) *
        Real.exp ((2 ^ n : ℕ) * Δ + ε * m) :=
      mul_le_mul_of_nonneg_left (hcost N V Δ hN hV) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
