import OAI.Combinatorics.EditApproximation.Geometry.PublishedInputs

namespace OAI

/-!
# Coarse threshold concentration from the published scalar input

The quantitative Bernstein bound used in Section 3 does not require
independence of estimated child values.
The random variables to which Bernstein is applied are fixed true-cost
threshold contributions, conditional on ancestor thresholds.
-/

namespace EditApproximation

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Numerical exponent estimate for the coarse estimator's choice of
deviation. The proof also covers the two regimes in the manuscript at once. -/
theorem coarse_bernstein_exponent {lam V allowance scale Q : ℝ}
    (hlam : 0 ≤ lam) (hlamone : lam ≤ 1) (hV : 0 ≤ V)
    (ha : 0 < allowance) (hu : 0 < scale) (hQ : Q * scale = allowance) :
    lam * Q / 12 ≤ (lam * V + allowance / 2) ^ 2 /
      (2 * scale * V + (2 / 3 : ℝ) * scale * (lam * V + allowance / 2)) := by
  let z := lam * V + allowance / 2
  have hz : 0 < z := by dsimp [z]; positivity
  have ha2 : allowance ≤ 2 * z := by dsimp [z]; nlinarith
  have hlamV : lam * V ≤ z := by dsimp [z]; linarith
  have hfirst : allowance * (lam * V) ≤ allowance * z :=
    mul_le_mul_of_nonneg_left hlamV ha.le
  have hsecond : lam * (allowance * z) ≤ allowance * z := by
    exact (mul_le_mul_of_nonneg_right hlamone (mul_nonneg ha.le hz.le)).trans_eq
      (one_mul _)
  have hthird : allowance * z ≤ 2 * z ^ 2 := by nlinarith
  have hbase : lam * allowance * (2 * V + (2 / 3 : ℝ) * z) ≤ 12 * z ^ 2 := by
    nlinarith [sq_nonneg z]
  have hdenom : 0 < 2 * scale * V + (2 / 3 : ℝ) * scale * z := by positivity
  apply (le_div_iff₀ hdenom).2
  change lam * Q / 12 * (2 * scale * V + (2 / 3 : ℝ) * scale * z) ≤ z ^ 2
  have heq : lam * Q / 12 * (2 * scale * V + (2 / 3 : ℝ) * scale * z) =
      lam * allowance * (2 * V + (2 / 3 : ℝ) * z) / 12 := by
    rw [← hQ]
    ring
  rw [heq]
  linarith

/-- Coarse threshold concentration, conditional only on the ancestor
data. Its hypotheses specify the centered *true-cost* random variables,
their moment proxy, and the threshold estimator's small bias. -/
theorem coarse_threshold_concentration {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (bernstein : FiniteBernsteinInput μ)
    {n : ℕ} (X : Fin n → Ω → ℝ) (estimator : Ω → ℝ)
    (mean V lam allowance scale Q : ℝ)
    (hlam : 0 ≤ lam) (hlamone : lam ≤ 1) (hV : 0 < V)
    (ha : 0 < allowance) (hu : 0 < scale) (hQ : Q * scale = allowance)
    (hscale : scale ≤ allowance / 2)
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hint : ∀ i, Integrable (X i) μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ scale)
    (hvariance : (∑ i, ∫ ω, (X i ω) ^ 2 ∂μ) ≤ scale * V)
    (hcenter : ∀ ω, estimator ω - mean = ∑ i, X i ω)
    (hbias : |mean - V| ≤ scale) :
    μ.real {ω | lam * V + allowance < |estimator ω - V|} ≤
      2 * Real.exp (-lam * Q / 12) := by
  let z := lam * V + allowance / 2
  have hz : 0 < z := by dsimp [z]; positivity
  have htail := bernstein n X scale (scale * V) z hu (mul_pos hu hV) hz
    hindep hmeas hint hmean hbound hvariance
  have hsubset : {ω | lam * V + allowance < |estimator ω - V|} ⊆
      {ω | z ≤ |∑ i, X i ω|} := by
    intro ω hω
    have htriangle : |estimator ω - V| ≤ |estimator ω - mean| + |mean - V| := by
      calc
        |estimator ω - V| = |(estimator ω - mean) + (mean - V)| := by
          congr 1
          ring
        _ ≤ |estimator ω - mean| + |mean - V| := abs_add_le _ _
    rw [hcenter ω] at htriangle
    change z ≤ |∑ i, X i ω|
    dsimp [z]
    have hω' : lam * V + allowance < |estimator ω - V| := hω
    linarith
  apply (measureReal_mono (μ := μ) hsubset).trans
  apply htail.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  have hexponent := coarse_bernstein_exponent hlam hlamone hV.le ha hu hQ
  change -z ^ 2 / (2 * (scale * V) + (2 / 3 : ℝ) * scale * z) ≤ -lam * Q / 12
  simpa only [neg_div, neg_mul, mul_assoc] using neg_le_neg hexponent

end EditApproximation

end OAI
