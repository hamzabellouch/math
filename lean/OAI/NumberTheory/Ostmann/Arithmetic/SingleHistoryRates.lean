import OAI.NumberTheory.Ostmann.Arithmetic.HarmonicHistorySupport
import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyBudgetRates
import OAI.NumberTheory.Ostmann.Arithmetic.LeafFrequencyBudget

namespace OAI

/-! # Cancellation of the single-history leaf frequency cost -/

namespace Ostmann

open Filter

/-- Unlike the two-history comparison, this cancels every leading copy
of Delta against the squared level-zero weight. -/
theorem single_leaf_frequency_cancellation (r V : ℕ) (Δ m K : ℝ)
    (hV : (V : ℝ) ≤ Real.exp (Δ + Real.sqrt m)) :
    (2 * (V : ℝ)) ^ r * Real.exp (-(r : ℝ) * Δ + K) ≤
      Real.exp ((r : ℝ) * Real.sqrt m + r * Real.log 2 + K) := by
  calc
    _ ≤ (2 * Real.exp (Δ + Real.sqrt m)) ^ r * Real.exp (-(r : ℝ) * Δ + K) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) _) (Real.exp_pos _).le
    _ = _ := by
      nth_rw 1 [show (2 : ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)]]
      rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

theorem single_leaf_frequency_budget_sublinear (r : ℕ) (K ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, ∀ m : ℝ, M ≤ m → ∀ Δ : ℝ, ∀ V : ℕ,
      (V : ℝ) ≤ Real.exp (Δ + Real.sqrt m) →
      (2 * (V : ℝ)) ^ r * Real.exp (-(r : ℝ) * Δ + K) ≤ Real.exp (ε * m) := by
  obtain ⟨M, hM⟩ := sqrt_cost_sublinear r (r * Real.log 2 + K) ε (by positivity) hε
  refine ⟨M, fun m hm Δ V hV => (single_leaf_frequency_cancellation r V Δ m K hV).trans ?_⟩
  apply Real.exp_le_exp.mpr
  linarith [hM m hm]

theorem single_frequency_budget_subexponential (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∃ D : ℝ, 1 ≤ D ∧
      (∀ n : ℕ, n ≠ 0 → (n : ℝ) ≤ Real.exp (2 * C * m) → (n.divisors.card : ℝ) ≤ D) ∧
      (∀ N : ℕ, (N : ℝ) ≤ Real.exp (C * m) →
        4 * D ^ 3 * (1 + Real.log N) ≤ Real.exp (ε * m)) := by
  filter_upwards [frequency_budget_subexponential C ε hC hε,
    eventually_ge_atTop (0 : ℝ)] with m hm hm0
  obtain ⟨D, hD, hdiv, hcost⟩ := hm
  have hD1 : 1 ≤ D := by
    have h1 := hdiv 1 (by norm_num) (by simpa using Real.one_le_exp (mul_nonneg (by positivity) hm0))
    simpa using h1
  refine ⟨D, hD1, hdiv, fun N hN => ?_⟩
  have hL : 1 ≤ 1 + Real.log N := by linarith [Real.log_natCast_nonneg N]
  have hpD : D ^ 3 ≤ D ^ 4 := pow_le_pow_right₀ hD1 (by norm_num)
  have hpL : 1 + Real.log N ≤ (1 + Real.log N) ^ 3 := by
    simpa using pow_le_pow_right₀ hL (show 1 ≤ 3 by norm_num)
  apply le_trans _ (hcost N hN)
  calc
    _ ≤ 8 * D ^ 3 * (1 + Real.log N) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hD 3)
    _ ≤ 8 * D ^ 4 * (1 + Real.log N) ^ 3 := by gcongr

/-- A single divisor bound works for every history and every permissible
frequency range. The numerical estimate is independent of its residue modulus. -/
theorem single_history_budget_parameters (n : ℕ) (K C ε : ℝ)
    (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∃ D : ℝ, 0 ≤ D ∧
      (∀ q : ℕ, q ≠ 0 → (q : ℝ) ≤ Real.exp (2 * C * m) → (q.divisors.card : ℝ) ≤ D) ∧
      (∀ N V : ℕ, ∀ Δ : ℝ, (N : ℝ) ≤ Real.exp (C * m) →
        (V : ℝ) ≤ Real.exp (Δ + Real.sqrt m) →
        Real.exp (-(2 ^ n : ℕ) * Δ + K) *
          ((4 * D ^ 3 * (1 + Real.log N)) ^ (2 ^ n - 1) * (2 * (V : ℝ)) ^ (2 ^ n)) ≤
            Real.exp (ε * m)) := by
  let r : ℕ := 2 ^ n
  let δ : ℝ := ε / (2 * r)
  have hr : (0 : ℝ) < r := by exact_mod_cast Nat.two_pow_pos n
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδr : δ * r = ε / 2 := by dsimp [δ]; field_simp
  obtain ⟨M, hM⟩ := single_leaf_frequency_budget_sublinear r K (ε / 2) (by positivity)
  filter_upwards [single_frequency_budget_subexponential C δ hC hδ,
    eventually_ge_atTop M, eventually_ge_atTop (0 : ℝ)] with m hrate hm hm0
  obtain ⟨D, hD, hdiv, hcost⟩ := hrate
  have hD0 : 0 ≤ D := le_trans (by norm_num) hD
  refine ⟨D, hD0, hdiv, fun N V Δ hN hV => ?_⟩
  have hnode : (4 * D ^ 3 * (1 + Real.log N)) ^ (r - 1) ≤ Real.exp ((ε / 2) * m) := by
    calc
      _ ≤ Real.exp (δ * m) ^ (r - 1) := pow_le_pow_left₀ (by
        have := Real.log_natCast_nonneg N
        positivity) (hcost N hN) _
      _ = Real.exp ((r - 1 : ℕ) * (δ * m)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hcount : ((r - 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le r 1
        have hh := mul_le_mul_of_nonneg_right hcount (mul_nonneg hδ.le hm0)
        nlinarith [hδr]
  have hleaf := hM m hm Δ V hV
  calc
    _ = (4 * D ^ 3 * (1 + Real.log N)) ^ (r - 1) *
        ((2 * (V : ℝ)) ^ r * Real.exp (-(r : ℝ) * Δ + K)) := by ring
    _ ≤ Real.exp ((ε / 2) * m) * Real.exp ((ε / 2) * m) :=
      mul_le_mul hnode hleaf (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The one-history arithmetic sum, including its square-weight factor,
is subexponential. This bound is uniform in the choice of residue modulus. -/
theorem single_arithmetic_support_rate {Q : ℕ} [NeZero Q]
    (n : ℕ) (K C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∀ N V : ℕ, ∀ Δ : ℝ, ∀ S : Finset ℤ,
      (N : ℝ) ≤ Real.exp (C * m) →
      (V : ℝ) ≤ Real.exp (Δ + Real.sqrt m) →
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) →
      ∀ data : FrequencyTree S n → (ZMod Q)ˣ → List (ZMod Q)ˣ → Option (ArithmeticSplitData Q),
      (∀ t P past d, data t P past = some d →
        d.hasFrequencies (singleTreeNodeFrequencies S n t past.length)) →
      Real.exp (-(2 ^ n : ℕ) * Δ + K) * singleArithmeticSupportSum S V n data ≤ Real.exp (ε * m) := by
  filter_upwards [single_history_budget_parameters n K C ε hC hε] with m hm
  obtain ⟨D, hD, hdiv, hbudget⟩ := hm
  intro N V Δ S hN hV hS data hmatch
  have hdivN (q : ℕ) (hq : q ≠ 0) (hqN : q ≤ N ^ 2) : (q.divisors.card : ℝ) ≤ D := by
    apply hdiv q hq
    calc
      (q : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hqN
      _ ≤ Real.exp (C * m) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2
      _ = Real.exp (2 * C * m) := by rw [← Real.exp_nat_mul]; congr 1; ring
  exact (mul_le_mul_of_nonneg_left
    (single_arithmetic_support_sum_le S N V n D hD hS hdivN data hmatch)
      (Real.exp_pos _).le).trans (hbudget N V Δ hN hV)

end Ostmann

end OAI
