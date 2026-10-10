import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget
import OAI.Combinatorics.Progressions.Probability.RecoveredChartMassLogBounds

namespace OAI

section

namespace Erdos3

theorem exists_recoveredChartMass_early_power (s a b : ℕ) :
    ∃ chartPower slowPower : ℕ, 2 ≤ chartPower ∧ 2 ≤ slowPower ∧
      ∀ p : ℝ, 2 ≤ p →
      let chartLog := (p + 2) ^ chartPower
      let slowLog := (p + 2) ^ slowPower
      (p + 2) ^ a ≤ chartLog ∧
      (∀ n : ℕ, (n : ℝ) ≤ Real.exp ((p + 2) ^ a) → (n : ℝ) ≤ Real.exp chartLog) ∧
      (∀ j n d : ℕ, (j : ℝ) ≤ p → (n : ℝ) ≤ Real.exp ((p + 2) ^ a) →
        (d : ℝ) ≤ p → ∀ C R : ℝ,
        C ∈ Set.Icc 0 (Real.exp ((p + 2) ^ a)) → R ∈ Set.Icc 0 1 →
        (j + 2 : ℝ) * (n + 1 : ℝ) ^ (j + 1) * C * (d + 1 : ℝ) * R ≤
          Real.exp chartLog) ∧
      ∀ n : ℕ, (n : ℝ) ≤ Real.exp ((p + 2) ^ a) →
        ∀ budget B : ℝ, budget ≤ (p + 2) ^ b → B ∈ Set.Icc 0 (Real.exp chartLog) →
        (s + 1 : ℝ) * (n + 1 : ℝ) ^ s * Real.exp budget * B ^ s ≤
          Real.exp slowLog := by
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ a
  let chart : Polynomial ℕ :=
    (Polynomial.X + 2) + (Polynomial.X + 2) * (Polynomial.X + Q + 1) + Q
  obtain ⟨chartPower, hchartPower, hchart⟩ := exists_natPolynomial_fixed_power_budget chart
  let slow : Polynomial ℕ := Polynomial.C (s + 1) + Polynomial.C s * (Q + 1) +
    (Polynomial.X + 2) ^ b + Polynomial.C s * (Polynomial.X + 2) ^ chartPower
  obtain ⟨slowPower, hslowPower, hslow⟩ := exists_natPolynomial_fixed_power_budget slow
  refine ⟨chartPower, slowPower, hchartPower, hslowPower, ?_⟩
  intro p hp chartLog slowLog
  let q := (p + 2) ^ a
  let L := p + q
  have hp0 : 0 ≤ p := by linarith
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hL0 : 0 ≤ L := add_nonneg hp0 hq0
  have hchart' : (p + 2) + (p + 2) * (L + 1) + q ≤ chartLog := by
    simpa [chart, Q, Polynomial.eval₂_pow, chartLog, L, q] using hchart p hp0
  have hqchart : q ≤ chartLog := by
    have hnonneg : 0 ≤ (p + 2) * (L + 1) := by positivity
    linarith
  have hslow' : (s + 1 : ℝ) + (s : ℝ) * (q + 1) + (p + 2) ^ b +
      (s : ℝ) * chartLog ≤ slowLog := by
    simpa [slow, Q, Polynomial.eval₂_pow, chartLog, slowLog, q] using hslow p hp0
  refine ⟨hqchart, ?_, ?_, ?_⟩
  · intro n hn
    exact hn.trans (Real.exp_le_exp.mpr hqchart)
  · intro j n d hj hn hd C R hC hR
    have hnL : (n : ℝ) ≤ Real.exp L := hn.trans (Real.exp_le_exp.mpr (by dsimp only [L]; linarith))
    have hdL : (d : ℝ) ≤ Real.exp L := by
      calc
        _ ≤ p := hd
        _ ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
        _ ≤ Real.exp L := Real.exp_le_exp.mpr (by dsimp only [L]; linarith)
    have hlog : (j + 2 : ℝ) + (j + 2 : ℝ) * (L + 1) + q ≤ chartLog := by
      have hmul : (j + 2 : ℝ) * (L + 1) ≤ (p + 2) * (L + 1) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      linarith
    have hraw : (j + 2 : ℝ) * (n + 1 : ℝ) ^ (j + 1) * C * (d + 1 : ℝ) * R ≤
        Real.exp ((j + 2 : ℝ) + (j + 2 : ℝ) * (L + 1) + q) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using
        recoveredChartMass_exp_bound j n d hL0 hnL hdL hC hR
    exact hraw.trans (Real.exp_le_exp.mpr hlog)
  · intro n hn budget B hbudget hB
    have hlog : (s + 1 : ℝ) + (s : ℝ) * (q + 1) + budget +
        (s : ℝ) * chartLog ≤ slowLog := by linarith
    have hraw : (s + 1 : ℝ) * (n + 1 : ℝ) ^ s * Real.exp budget * B ^ s ≤
        Real.exp ((s + 1 : ℝ) + (s : ℝ) * (q + 1) + budget + (s : ℝ) * chartLog) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        recoveredSlowChartMass_exp_bound s n (budget := budget) hq0 hn hB
    exact hraw.trans (Real.exp_le_exp.mpr hlog)

end Erdos3

end

end OAI
