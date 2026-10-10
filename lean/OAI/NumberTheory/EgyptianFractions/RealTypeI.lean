import OAI.NumberTheory.EgyptianFractions.RationalPhaseHyperbola
import OAI.NumberTheory.EgyptianFractions.RealPhaseEnvelope
import OAI.NumberTheory.EgyptianFractions.LogWeightedSums

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RealTypeI

open RationalPhaseSpacing

lemma geometric_envelope_le_truncated_real (t : ℝ) (M : ℕ) (cap : ℝ)
    (hM : (M : ℝ) ≤ cap) :
    RealPhase.envelope M t ≤ truncatedInv cap (intDistance t) := by
  have heq : RealPhase.integerDistance t = intDistance t := abs_sub_round_eq_min t
  unfold RealPhase.envelope
  rw [heq]
  unfold truncatedInv
  split_ifs with hzero
  · exact hM
  · have hd : 0 < intDistance t :=
      lt_of_le_of_ne (intDistance_nonneg _) (Ne.symm hzero)
    exact min_le_min hM (one_div_le_one_div_of_le hd (by linarith))

/-- The geometric envelope is bounded by the reciprocal-distance envelope
used in the rational-approximation argument, also at an integer frequency. -/
lemma geometric_envelope_le_truncated (t : ℝ) (M H : ℕ) (hMH : M ≤ H) :
    RealPhase.envelope M t ≤ truncatedInv (H : ℝ) (intDistance t) := by
  exact geometric_envelope_le_truncated_real t M H (by exact_mod_cast hMH)

/-- Actual near-rational Type I estimate on any integer interval, allowing
different inner lengths, starting points and constant phases at every index. -/
theorem sum_norm_phase_sums_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (L : ℤ) (N H : ℕ) (length : ℤ → ℕ) (start shift : ℤ → ℝ)
    (hlength : ∀ n ∈ Finset.Ico L (L + N), length n ≤ H) :
    (∑ n ∈ Finset.Ico L (L + N),
      ‖∑ j ∈ Finset.range (length n),
        RealPhase.phase ((α * (n : ℝ)) * (start n + j) + shift n)‖) ≤
      (2 * (N : ℝ) / q + 1) *
        (2 * (H : ℝ) + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ)))) := by
  calc
    _ ≤ ∑ n ∈ Finset.Ico L (L + N), truncatedInv (H : ℝ) (intDistance (α * n)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact (RealPhase.norm_sum_shift_phase_le_envelope (α * n) (shift n) (start n)
        (length n)).trans (geometric_envelope_le_truncated _ _ _ (hlength n hn))
    _ ≤ _ := sum_truncatedInv_intDistance_interval_le α a q hq hcop happrox L N H
      (by positivity)

/-- Bounded coefficients and hyperbolic or otherwise varying inner intervals
require no extra cancellation hypothesis. -/
theorem norm_weighted_phase_sums_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (L : ℤ) (N H : ℕ) (length : ℤ → ℕ) (start shift : ℤ → ℝ)
    (hlength : ∀ n ∈ Finset.Ico L (L + N), length n ≤ H)
    (weight : ℤ → ℂ) (W : ℝ) (hW : 0 ≤ W)
    (hweight : ∀ n ∈ Finset.Ico L (L + N), ‖weight n‖ ≤ W) :
    ‖∑ n ∈ Finset.Ico L (L + N), weight n *
      ∑ j ∈ Finset.range (length n),
        RealPhase.phase ((α * (n : ℝ)) * (start n + j) + shift n)‖ ≤
      W * ((2 * (N : ℝ) / q + 1) *
        (2 * (H : ℝ) + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))))) := by
  calc
    _ ≤ ∑ n ∈ Finset.Ico L (L + N), ‖weight n *
        ∑ j ∈ Finset.range (length n),
          RealPhase.phase ((α * (n : ℝ)) * (start n + j) + shift n)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ico L (L + N), W *
        ‖∑ j ∈ Finset.range (length n),
          RealPhase.phase ((α * (n : ℝ)) * (start n + j) + shift n)‖ := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hweight n hn) (norm_nonneg _)
    _ = W * (∑ n ∈ Finset.Ico L (L + N),
        ‖∑ j ∈ Finset.range (length n),
          RealPhase.phase ((α * (n : ℝ)) * (start n + j) + shift n)‖) :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_norm_phase_sums_le α a q hq hcop happrox L N H length start shift hlength) hW

/-- The explicit scalar cost of a hyperbolic Type I sum. -/
def hyperbolicCost (X : ℝ) (M q : ℕ) : ℝ :=
  8 * ((M : ℝ) + q) * (1 + Real.log (2 * (q : ℝ))) +
    (4 * X / (q : ℝ)) * (1 + Real.log ((M : ℝ) + 1))

/-- The actual geometric sums with inner lengths at most `X/n` have the
power-saving hyperbolic cost, rather than the ineffective common-cap cost. -/
theorem sum_norm_hyperbolic_phase_sums_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (X : ℝ) (hX : 0 ≤ X) (M : ℕ) (length : ℤ → ℕ) (start shift : ℤ → ℝ)
    (hlength : ∀ n ∈ Finset.Icc 1 (M : ℤ), (length n : ℝ) ≤ X / (n : ℝ)) :
    (∑ n ∈ Finset.Icc 1 (M : ℤ),
      ‖∑ j ∈ Finset.range (length n),
        RealPhase.phase ((α * (n : ℝ)) * (start n + j) + shift n)‖) ≤
      hyperbolicCost X M q := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 (M : ℤ),
        truncatedInv (X / (n : ℝ)) (intDistance (α * n)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact (RealPhase.norm_sum_shift_phase_le_envelope (α * n) (shift n) (start n)
        (length n)).trans (geometric_envelope_le_truncated_real _ _ _ (hlength n hn))
    _ ≤ _ := sum_truncatedInv_hyperbolic_le α a q hq hcop happrox X hX M

theorem norm_weighted_hyperbolic_phase_sums_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (X : ℝ) (hX : 0 ≤ X) (M : ℕ) (length : ℤ → ℕ) (start shift : ℤ → ℝ)
    (hlength : ∀ n ∈ Finset.Icc 1 (M : ℤ), (length n : ℝ) ≤ X / (n : ℝ))
    (weight : ℤ → ℂ) (W : ℝ) (hW : 0 ≤ W)
    (hweight : ∀ n ∈ Finset.Icc 1 (M : ℤ), ‖weight n‖ ≤ W) :
    ‖∑ n ∈ Finset.Icc 1 (M : ℤ), weight n *
      ∑ j ∈ Finset.range (length n),
        RealPhase.phase ((α * (n : ℝ)) * (start n + j) + shift n)‖ ≤
      W * hyperbolicCost X M q := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 (M : ℤ), ‖weight n *
        ∑ j ∈ Finset.range (length n),
          RealPhase.phase ((α * (n : ℝ)) * (start n + j) + shift n)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 (M : ℤ), W *
        ‖∑ j ∈ Finset.range (length n),
          RealPhase.phase ((α * (n : ℝ)) * (start n + j) + shift n)‖ := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hweight n hn) (norm_nonneg _)
    _ = W * (∑ n ∈ Finset.Icc 1 (M : ℤ),
        ‖∑ j ∈ Finset.range (length n),
          RealPhase.phase ((α * (n : ℝ)) * (start n + j) + shift n)‖) :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_norm_hyperbolic_phase_sums_le α a q hq hcop happrox X hX M length start shift
        hlength) hW

/-- Logarithmic inner weights cost at most `2 log(X+1)` in the true
hyperbolic Type I estimate. The zero-length case is included. -/
theorem sum_norm_log_hyperbolic_phase_sums_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (X : ℝ) (hX : 0 ≤ X) (M : ℕ) (length : ℤ → ℕ)
    (hlength : ∀ n ∈ Finset.Icc 1 (M : ℤ), (length n : ℝ) ≤ X / (n : ℝ)) :
    (∑ n ∈ Finset.Icc 1 (M : ℤ),
      ‖∑ j ∈ Finset.range (length n),
        (Real.log (j + 1 : ℕ) : ℂ) *
          RealPhase.phase ((α * (n : ℝ)) * (j + 1 : ℕ))‖) ≤
      (2 * Real.log (X + 1)) * hyperbolicCost X M q := by
  have hlogX : 0 ≤ Real.log (X + 1) := Real.log_nonneg (by linarith)
  have hpoint (n : ℤ) (hn : n ∈ Finset.Icc 1 (M : ℤ)) :
      ‖∑ j ∈ Finset.range (length n),
        (Real.log (j + 1 : ℕ) : ℂ) *
          RealPhase.phase ((α * (n : ℝ)) * (j + 1 : ℕ))‖ ≤
      (2 * Real.log (X + 1)) * truncatedInv (X / (n : ℝ)) (intDistance (α * n)) := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnp : (0 : ℝ) < n := by linarith
    have hcap : 0 ≤ X / (n : ℝ) := div_nonneg hX hnp.le
    have hB : 0 ≤ truncatedInv (X / (n : ℝ)) (intDistance (α * n)) :=
      truncatedInv_nonneg hcap (intDistance_nonneg _)
    have hprefix : ∀ k ≤ length n,
        ‖∑ j ∈ Finset.range k, RealPhase.phase ((α * (n : ℝ)) * (j + 1 : ℕ))‖ ≤
          truncatedInv (X / (n : ℝ)) (intDistance (α * n)) := by
      intro k hk
      have hkcap : (k : ℝ) ≤ X / (n : ℝ) :=
        (by exact_mod_cast hk : (k : ℝ) ≤ length n).trans (hlength n hn)
      have h := (RealPhase.norm_sum_shift_phase_le_envelope (α * (n : ℝ)) 0 1 k).trans
        (geometric_envelope_le_truncated_real _ _ _ hkcap)
      simpa only [Nat.cast_add, Nat.cast_one, add_zero, add_comm (1 : ℝ)] using h
    have hs := Vaughan.norm_log_weighted_range_le
      (fun j : ℕ => RealPhase.phase ((α * (n : ℝ)) * j)) (length n)
      (truncatedInv (X / (n : ℝ)) (intDistance (α * n))) hprefix
    have hloglen : Real.log (length n : ℝ) ≤ Real.log (X + 1) := by
      by_cases hz : length n = 0
      · simpa only [hz, Nat.cast_zero, Real.log_zero] using hlogX
      · apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz)
        have hdiv : X / (n : ℝ) ≤ X := by
          apply (div_le_iff₀ hnp).mpr
          nlinarith
        exact (hlength n hn).trans (hdiv.trans (by linarith))
    exact hs.trans (mul_le_mul_of_nonneg_right (by linarith) hB)
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 (M : ℤ),
        (2 * Real.log (X + 1)) * truncatedInv (X / (n : ℝ)) (intDistance (α * n)) :=
      Finset.sum_le_sum hpoint
    _ = (2 * Real.log (X + 1)) *
        ∑ n ∈ Finset.Icc 1 (M : ℤ), truncatedInv (X / (n : ℝ)) (intDistance (α * n)) :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_truncatedInv_hyperbolic_le α a q hq hcop happrox X hX M) (by positivity)

theorem norm_weighted_log_hyperbolic_phase_sums_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (X : ℝ) (hX : 0 ≤ X) (M : ℕ) (length : ℤ → ℕ)
    (hlength : ∀ n ∈ Finset.Icc 1 (M : ℤ), (length n : ℝ) ≤ X / (n : ℝ))
    (weight : ℤ → ℂ) (W : ℝ) (hW : 0 ≤ W)
    (hweight : ∀ n ∈ Finset.Icc 1 (M : ℤ), ‖weight n‖ ≤ W) :
    ‖∑ n ∈ Finset.Icc 1 (M : ℤ), weight n *
      ∑ j ∈ Finset.range (length n),
        (Real.log (j + 1 : ℕ) : ℂ) *
          RealPhase.phase ((α * (n : ℝ)) * (j + 1 : ℕ))‖ ≤
      W * ((2 * Real.log (X + 1)) * hyperbolicCost X M q) := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 (M : ℤ), ‖weight n *
        ∑ j ∈ Finset.range (length n),
          (Real.log (j + 1 : ℕ) : ℂ) *
            RealPhase.phase ((α * (n : ℝ)) * (j + 1 : ℕ))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 (M : ℤ), W *
        ‖∑ j ∈ Finset.range (length n),
          (Real.log (j + 1 : ℕ) : ℂ) *
            RealPhase.phase ((α * (n : ℝ)) * (j + 1 : ℕ))‖ := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hweight n hn) (norm_nonneg _)
    _ = W * (∑ n ∈ Finset.Icc 1 (M : ℤ),
        ‖∑ j ∈ Finset.range (length n),
          (Real.log (j + 1 : ℕ) : ℂ) *
            RealPhase.phase ((α * (n : ℝ)) * (j + 1 : ℕ))‖) :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_norm_log_hyperbolic_phase_sums_le α a q hq hcop happrox X hX M length hlength) hW

end Problem337.RealTypeI

end

end OAI
