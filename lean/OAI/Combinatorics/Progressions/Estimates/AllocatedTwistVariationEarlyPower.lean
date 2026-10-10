import OAI.Combinatorics.Progressions.Probability.SupportedRecoveredChartMassEarlyPower

namespace OAI

section

namespace Erdos3
open scoped NNReal

theorem exists_allocatedTwistVariation_early_power (a b : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ p : ℝ, 2 ≤ p →
      ∀ m localDim : ℕ, (m : ℝ) ≤ p → (localDim : ℝ) ≤ (p + 2) ^ a →
      ∀ (L : ℝ≥0) (modulus cover : ℕ),
      (L : ℝ) ≤ Real.exp ((p + 2) ^ b) →
      (modulus : ℝ) ≤ Real.exp ((p + 2) ^ b) →
      (cover : ℝ) ≤ Real.exp ((p + 2) ^ b) →
      (L : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
        ((localDim + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp ((p + 2) ^ E) ∧
      ((modulus * cover : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ E) := by
  obtain ⟨A, _hA, hmass⟩ := exists_supportedRecoveredChartMass_polynomial_power 0 a 0
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ b
  let R : Polynomial ℕ := Q + Polynomial.X + 1 + (Polynomial.X + 2) ^ A
  obtain ⟨E, hE, hbudget⟩ := exists_natPolynomial_fixed_power_budget (R + 2 * Q)
  refine ⟨E, hE, ?_⟩
  intro p hp m localDim hm hn L modulus cover hL hmod hcover
  let q := (p + 2) ^ b
  let t := (p + 2) ^ A
  let mass : ℝ := (m + 1 : ℝ) * (localDim + 1 : ℝ) ^ m
  have hp0 : 0 ≤ p := by linarith
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have ht0 : 0 ≤ t := by dsimp only [t]; positivity
  have hsum : (q + p + 1 + t) + 2 * q ≤ (p + 2) ^ E := by
    simpa [R, Q, Polynomial.eval₂_pow, q, t] using hbudget p hp0
  have hvarLog : q + p + 1 + t ≤ (p + 2) ^ E := by linarith
  have hperiodLog : 2 * q ≤ (p + 2) ^ E := by linarith
  have hmassBound : mass ≤ Real.exp t :=
    (hmass p hp localDim 0 m hn (by
      simpa only [Nat.cast_zero] using pow_nonneg (by linarith : 0 ≤ p + 2) a) hm).1
  have hmassOne : 1 ≤ mass := by
    dsimp only [mass]
    exact one_le_mul_of_one_le_of_one_le (by linarith [Nat.cast_nonneg (α := ℝ) m])
      (one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) localDim] :
        (1 : ℝ) ≤ localDim + 1))
  have hfactor : 1 + (m : ℝ) * mass ≤ Real.exp (p + 1 + t) := by
    calc
      _ ≤ (p + 1) * mass := by nlinarith [mul_le_mul_of_nonneg_right hm (by linarith : 0 ≤ mass)]
      _ ≤ Real.exp (p + 1) * Real.exp t := by
        apply mul_le_mul _ hmassBound (by linarith) (Real.exp_nonneg _)
        linarith [Real.add_one_le_exp (p + 1)]
      _ = _ := (Real.exp_add _ _).symm
  constructor
  · have hproduct : (L : ℝ) * (1 + (m : ℝ) * mass) ≤ Real.exp (q + p + 1 + t) := by
      calc
        _ ≤ Real.exp q * Real.exp (p + 1 + t) :=
          mul_le_mul hL hfactor (by positivity) (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hfinal := hproduct.trans (Real.exp_le_exp.mpr hvarLog)
    simpa only [mass, Nat.cast_add, Nat.cast_one] using hfinal
  · calc
      _ = (modulus : ℝ) * (cover : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp q * Real.exp q :=
        mul_le_mul hmod hcover (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * q) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hperiodLog

end Erdos3

end

end OAI
