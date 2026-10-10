import OAI.Combinatorics.EditApproximation.Geometry.NodeRegret
import OAI.Combinatorics.EditApproximation.Probability.SampledRegret

namespace OAI

/-!
# Averaging the first-crossing regret

All parent random choices may be represented by one finite uniform sample.
Only the separate marginal laws of online draws and group failures are
used. In particular, these two families may be correlated with one another.
-/

namespace EditApproximation

open Finset

theorem firstCrossing_expected_sum_bound {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (S crossing : ℕ) (regret prefixPayoff failure : Ω → ℕ → ℝ)
    (prefixBudget crossingCharge failureCharge q : ℝ)
    (hcrossing : crossing ≤ S) (hcharge : 0 ≤ crossingCharge) (hfailureCharge : 0 ≤ failureCharge)
    (hfailure : ∀ ω t, t < S → 0 ≤ failure ω t)
    (hprefix : ∀ ω t, t < crossing → regret ω t ≤ prefixPayoff ω t + failureCharge * failure ω t)
    (hcross : ∀ ω, crossing < S → regret ω crossing ≤ crossingCharge + failureCharge * failure ω crossing)
    (hafter : ∀ ω t, t < S → crossing < t → regret ω t ≤ 0)
    (hprefixMean : (∑ t ∈ range crossing, uniformMean (fun ω => prefixPayoff ω t)) ≤ prefixBudget)
    (hfailureMean : ∀ t < S, uniformMean (fun ω => failure ω t) ≤ q) :
    uniformMean (fun ω => ∑ t ∈ range S, regret ω t) ≤
      prefixBudget + crossingCharge + failureCharge * (S : ℝ) * q := by
  have hpoint ω := firstCrossing_sum_bound S crossing (regret ω) (prefixPayoff ω)
    (failure ω) crossingCharge failureCharge hcrossing hcharge hfailureCharge
    (hfailure ω) (hprefix ω) (hcross ω) (hafter ω)
  have hmean := uniformMean_mono _ _ hpoint
  simp only [uniformMean_add, uniformMean_const, uniformMean_mul, uniformMean_sum] at hmean ⊢
  have hfailSum : (∑ t ∈ range S, uniformMean (fun ω => failure ω t)) ≤ (S : ℝ) * q := by
    have hsum := sum_le_sum (s := range S) fun t ht => hfailureMean t (mem_range.mp ht)
    simpa only [sum_const, card_range, nsmul_eq_mul] using hsum
  have hfailCost := mul_le_mul_of_nonneg_left hfailSum hfailureCharge
  nlinarith

/-- Integrating a fixed child-table environment uses only finite linearity.
The failure cost is the manuscript's `2 S H^-4 F c`. -/
theorem node_expected_failure_charge {S H : ℕ} {F c failureBudget : ℝ}
    (hF : 0 ≤ F) (hc : 0 ≤ c)
    (hbudget : failureBudget ≤ (S : ℝ) / (H : ℝ) ^ 4) :
    2 * F * c * failureBudget ≤ 2 * S * (1 / (H : ℝ) ^ 4) * F * c := by
  have hmul := mul_le_mul_of_nonneg_left hbudget (by positivity : 0 ≤ 2 * F * c)
  convert hmul using 1; ring

end EditApproximation

end OAI
