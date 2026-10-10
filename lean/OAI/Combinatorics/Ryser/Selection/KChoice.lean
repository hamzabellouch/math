import OAI.Combinatorics.Ryser.Selection.AnalyticalLimits
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

open Filter Topology

namespace RyserCoveringCounterexample.Selection

theorem tendsto_small_certificate_coefficient (A : ℝ) :
    Tendsto (fun K : ℕ => A * (K : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (K - 3))
      atTop (𝓝 0) := by
  have hbase : Tendsto
      (fun K : ℕ => (8 * A) * ((K : ℝ) ^ 2 * (1 / 2 : ℝ) ^ K))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_const_mul_const_pow_of_lt_one 2
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul
        (8 * A)
  refine hbase.congr' ?_
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with K hK
  have hpow : (1 / 2 : ℝ) ^ (K - 3) = 8 * (1 / 2 : ℝ) ^ K := by
    rw [pow_sub₀ (1 / 2 : ℝ) (by norm_num) hK]
    norm_num
    ring
  rw [hpow]
  ring

theorem tendsto_large_certificate_coefficient (B : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun K : ℕ => B * (K : ℝ) ^ 2 * Real.exp (2 - (K : ℝ) * δ))
      atTop (𝓝 0) := by
  have hbase : Tendsto
      (fun K : ℕ => (B * Real.exp 2) *
        ((K : ℝ) ^ 2 * Real.exp (-δ * (K : ℝ))))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_nat_pow_mul_exp_neg_mul 2 hδ).const_mul (B * Real.exp 2)
  refine hbase.congr' (Eventually.of_forall fun K : ℕ => ?_)
  change (B * Real.exp 2) * ((K : ℝ) ^ 2 * Real.exp (-δ * (K : ℝ))) =
    B * (K : ℝ) ^ 2 * Real.exp (2 - (K : ℝ) * δ)
  have hexponent : 2 - (K : ℝ) * δ = 2 + (-δ * (K : ℝ)) := by ring
  rw [hexponent, Real.exp_add]
  ring

theorem exists_pool_size (A B : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℕ, 6 ≤ K ∧
      A * (K : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (K - 3) ≤ 1 / 2 ∧
      B * (K : ℝ) ^ 2 * Real.exp (2 - (K : ℝ) * δ) < 1 / 2 := by
  have hsmall : ∀ᶠ K : ℕ in atTop,
      A * (K : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (K - 3) < 1 / 2 :=
    (tendsto_small_certificate_coefficient A).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hlarge : ∀ᶠ K : ℕ in atTop,
      B * (K : ℝ) ^ 2 * Real.exp (2 - (K : ℝ) * δ) < 1 / 2 :=
    (tendsto_large_certificate_coefficient B hδ).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hboth : ∀ᶠ K : ℕ in atTop, 6 ≤ K ∧
      A * (K : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (K - 3) ≤ 1 / 2 ∧
      B * (K : ℝ) ^ 2 * Real.exp (2 - (K : ℝ) * δ) < 1 / 2 := by
    filter_upwards [eventually_ge_atTop (6 : ℕ), hsmall, hlarge] with K hK hs hl
    exact ⟨hK, hs.le, hl⟩
  exact hboth.exists

end RyserCoveringCounterexample.Selection

end OAI
