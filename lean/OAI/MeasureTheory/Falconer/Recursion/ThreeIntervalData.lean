import OAI.MeasureTheory.Falconer.Recursion.ThreeIntervalProduct
import Mathlib.Tactic.IntervalCases

namespace OAI

/-! # The actual four dyadic depths and three collision factors -/

namespace Falconer
open scoped ENNReal BigOperators

def threeIntervalDepth (a b N j : ℕ) : ℕ :=
  if j = 0 then 0 else if j = 1 then a else if j = 2 then b else N

theorem threeIntervalDepth_le {a b N : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {j : ℕ} (hj : j ≤ 3) : threeIntervalDepth a b N j ≤ N := by
  interval_cases j <;> norm_num [threeIntervalDepth] <;> omega

theorem threeIntervalDepth_mono {a b N : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {j : ℕ} (hj : j < 3) : threeIntervalDepth a b N j ≤ threeIntervalDepth a b N (j+1) := by
  interval_cases j <;> norm_num [threeIntervalDepth] <;> assumption

theorem threeIntervalDepth_child {a b N : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {j : ℕ} (hj : j < 3) : a ≤ threeIntervalDepth a b N (j+1) := by
  interval_cases j <;> norm_num [threeIntervalDepth] <;> omega

noncomputable def threeIntervalFactor (a b N J : ℕ) (q c η : ℝ) (j : ℕ) : ℝ≥0∞ :=
  if j = 0 then ENNReal.ofReal (((2:ℝ)^N)^(10*η)*((2:ℝ)^a)^(-q))
  else if j = 1 then ENNReal.ofReal ((1/(2:ℝ)^((b-a)-J))^(q+c))
  else ENNReal.ofReal (((2:ℝ)^N)^(10*η)*((2:ℝ)^(N-b))^(-q))

theorem threeIntervalFactor_product {a b N J : ℕ}
    (hab : a ≤ b) (hbN : b ≤ N) (hJ : J ≤ b-a)
    {q c β γ η ξ : ℝ} (hc : 0 ≤ c)
    (hwidth : β*(N:ℝ) ≤ (b-a:ℕ))
    (hconst : ((2:ℝ)^J)^(q+c) ≤ ((2:ℝ)^N)^ξ)
    (hbudget : 20*η+4*ξ+γ ≤ c*β) :
    (∏ j ∈ Finset.range 3, (ENNReal.ofReal (((2:ℝ)^N)^(-ξ)))⁻¹*
      threeIntervalFactor a b N J q c η j) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-q-γ)) := by
  simpa [Finset.prod_range_succ,threeIntervalFactor] using
    three_interval_density_product_bound hab hbN hJ hc hwidth hconst hbudget

end Falconer

end OAI
