import Mathlib
import OAI.Probability.ThorpCompatibility.BinomialBounds

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
open Finset
lemma clump_exp_moment_simple {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (H z : ℝ) (hH : 0 ≤ H) (hn : 0 < Fintype.card β)
    (hsmall : Real.exp 2 * Fintype.card α *
      (Real.exp z * (Real.exp 1 / Fintype.card β)) ≤ H) :
    uniformMean (fun r : α → Equiv.Perm β => Real.exp (z * clumpCount H r)) ≤
      Real.exp ((Fintype.card β : ℝ) ^ 2 * (Fintype.card α + 1) * Real.exp (-H)) := by
  have hbin := binomial_large_size_sum (Fintype.card α) H
    (Real.exp z * (Real.exp 1 / Fintype.card β)) hH (by positivity) hsmall
  have hsum : (∑ s : Finset α, clumpWeight H z s *
      (Real.exp 1 / Fintype.card β) ^ s.card) ≤
        1 + (Fintype.card α + 1 : ℕ) * Real.exp (-H) := by
    rw [clump_subset_sum]
    exact hbin
  calc
    _ ≤ _ := clump_exp_moment_le H z hH hn
    _ ≤ (1 + (Fintype.card α + 1 : ℕ) * Real.exp (-H)) ^ (Fintype.card β ^ 2) := by
      apply pow_le_pow_left₀ _ hsum
      exact Finset.sum_nonneg fun s _ => mul_nonneg (clumpWeight_nonneg _ _ _) (by positivity)
    _ ≤ (Real.exp ((Fintype.card α + 1 : ℕ) * Real.exp (-H))) ^ (Fintype.card β ^ 2) := by
      apply pow_le_pow_left₀ (by positivity)
      simpa only [add_comm] using
        Real.add_one_le_exp ((Fintype.card α + 1 : ℕ) * Real.exp (-H))
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

end ThorpCompatibility

end OAI
