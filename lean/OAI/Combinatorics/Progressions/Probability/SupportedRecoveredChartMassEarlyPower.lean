import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget
import OAI.Combinatorics.Progressions.Probability.RecoveredChartMassLogBounds

namespace OAI

section

namespace Erdos3

theorem exists_supportedRecoveredChartMass_early_power (s a b : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ p : ℝ, 2 ≤ p →
      ∀ localDim fullDim m : ℕ,
      (localDim : ℝ) ≤ Real.exp ((p + 2) ^ a) →
      (fullDim : ℝ) ≤ Real.exp ((p + 2) ^ a) → (m : ℝ) ≤ p →
      let mass := (m + 1 : ℝ) * (localDim + 1 : ℝ) ^ m
      mass ≤ Real.exp ((p + 2) ^ E) ∧
      ∀ budget B : ℝ, budget ≤ (p + 2) ^ b → B ∈ Set.Icc 0 mass →
        (s + 1 : ℝ) * (fullDim + 1 : ℝ) ^ s * Real.exp budget * B ^ s ≤
          Real.exp ((p + 2) ^ E) := by
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ a
  let chart : Polynomial ℕ := (Polynomial.X + 1) + Polynomial.X * (Q + 1)
  let slow : Polynomial ℕ := Polynomial.C (s + 1) + Polynomial.C s * (Q + 1) +
    (Polynomial.X + 2) ^ b + Polynomial.C s * chart
  obtain ⟨E, hE, hbudget⟩ := exists_natPolynomial_fixed_power_budget (chart + slow)
  refine ⟨E, hE, ?_⟩
  intro p hp localDim fullDim m hlocal hfull hm mass
  let q := (p + 2) ^ a
  let chartLog := (p + 1) + p * (q + 1)
  let slowLog := (s + 1 : ℝ) + (s : ℝ) * (q + 1) + (p + 2) ^ b + (s : ℝ) * chartLog
  have hp0 : 0 ≤ p := by linarith
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hchart0 : 0 ≤ chartLog := by dsimp only [chartLog]; positivity
  have hslow0 : 0 ≤ slowLog := by dsimp only [slowLog]; positivity
  have hsum : chartLog + slowLog ≤ (p + 2) ^ E := by
    simpa [chart, slow, Q, Polynomial.eval₂_pow, chartLog, slowLog, q] using hbudget p hp0
  have hchartBound : chartLog ≤ (p + 2) ^ E := by linarith
  have hslowBound : slowLog ≤ (p + 2) ^ E := by linarith
  have hmassLog : mass ≤ Real.exp chartLog := by
    have hraw := recoveredSlowChartMass_exp_bound m localDim (L := q) (A := 0)
      (B := 1) (budget := 0) hq0 hlocal (by simp)
    have hraw' : mass ≤ Real.exp ((m + 1 : ℝ) + (m : ℝ) * (q + 1)) := by
      simpa only [mass, Real.exp_zero, one_pow, mul_one, mul_zero, add_zero,
        Nat.cast_add, Nat.cast_one] using hraw
    apply hraw'.trans (Real.exp_le_exp.mpr ?_)
    dsimp only [chartLog]
    have hmul := mul_le_mul_of_nonneg_right hm (show 0 ≤ q + 1 by linarith)
    linarith
  refine ⟨hmassLog.trans (Real.exp_le_exp.mpr hchartBound), ?_⟩
  intro budget B hbudgetB hB
  have hB' : B ∈ Set.Icc 0 (Real.exp chartLog) := ⟨hB.1, hB.2.trans hmassLog⟩
  have hraw := recoveredSlowChartMass_exp_bound s fullDim (L := q) (budget := budget) hq0 hfull hB'
  have hraw' : (s + 1 : ℝ) * (fullDim + 1 : ℝ) ^ s * Real.exp budget * B ^ s ≤
      Real.exp ((s + 1 : ℝ) + (s : ℝ) * (q + 1) + budget + (s : ℝ) * chartLog) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hraw
  apply hraw'.trans (Real.exp_le_exp.mpr ?_)
  dsimp only [slowLog] at hslowBound
  linarith

theorem exists_supportedRecoveredChartMass_polynomial_power (s a b : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ p : ℝ, 2 ≤ p →
      ∀ localDim fullDim m : ℕ,
      (localDim : ℝ) ≤ (p + 2) ^ a → (fullDim : ℝ) ≤ (p + 2) ^ a → (m : ℝ) ≤ p →
      let mass := (m + 1 : ℝ) * (localDim + 1 : ℝ) ^ m
      mass ≤ Real.exp ((p + 2) ^ E) ∧
      ∀ budget : ℝ, budget ≤ (p + 2) ^ b →
        (s + 1 : ℝ) * (fullDim + 1 : ℝ) ^ s * Real.exp budget * mass ^ s ≤
          Real.exp ((p + 2) ^ E) := by
  obtain ⟨E, hE, hbound⟩ := exists_supportedRecoveredChartMass_early_power s a b
  refine ⟨E, hE, ?_⟩
  intro p hp localDim fullDim m hlocal hfull hm mass
  have hexp : (p + 2) ^ a ≤ Real.exp ((p + 2) ^ a) := by
    linarith [Real.add_one_le_exp ((p + 2) ^ a)]
  obtain ⟨hmass, hslow⟩ :=
    hbound p hp localDim fullDim m (hlocal.trans hexp) (hfull.trans hexp) hm
  refine ⟨hmass, ?_⟩
  intro budget hbudget
  exact hslow budget mass hbudget ⟨by dsimp only [mass]; positivity, le_rfl⟩

end Erdos3

end

end OAI
