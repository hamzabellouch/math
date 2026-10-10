import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace OAI

/-!
# Absorbing the finite product of local moment bounds

The local factors in Section 3 of paper 031-01 are uniformly bounded.
For every positive exponent, their product over distinct prime divisors
of the saturation index is therefore bounded by a constant times that
index to the given exponent. This elementary argument also works for
any finite set of distinct positive integers.
-/

open Filter
open scoped BigOperators

namespace DukePrimeDegree

/-- A finite product of uniformly bounded factors has arbitrarily small
power growth in the product of its distinct positive integer labels. -/
theorem prod_le_subpower_of_uniform_bound
    (f : ℕ → ℝ) (B ε : ℝ) (hB : 1 ≤ B) (hε : 0 < ε)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : Finset ℕ, (∀ p ∈ s, 1 ≤ p) →
      (∏ p ∈ s, f p) ≤ C * (∏ p ∈ s, (p : ℝ)) ^ ε := by
  have hpow : Tendsto (fun p : ℕ => (p : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hpow.eventually (eventually_ge_atTop B))
  refine ⟨B ^ N, pow_pos (lt_of_lt_of_le zero_lt_one hB) _, ?_⟩
  intro s hs
  have hcard : (s.filter (· < N)).card ≤ N := by
    calc
      (s.filter (· < N)).card ≤ (Finset.range N).card :=
        Finset.card_le_card (fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = N := Finset.card_range N
  calc
    (∏ p ∈ s, f p) ≤
        ∏ p ∈ s, (if p < N then B else 1) * (p : ℝ) ^ ε := by
      apply Finset.prod_le_prod₀ (fun p _ => (hf p).1)
      intro p hp
      have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hs p hp
      split_ifs with hsmall
      · exact (hf p).2.trans (le_mul_of_one_le_right (zero_le_one.trans hB)
          (Real.one_le_rpow hp' hε.le))
      · simpa only [one_mul] using (hf p).2.trans (hN p (Nat.le_of_not_gt hsmall))
    _ = B ^ (s.filter (· < N)).card * (∏ p ∈ s, (p : ℝ)) ^ ε := by
      rw [Finset.prod_mul_distrib, Real.finsetProd_rpow]
      · simp [Finset.prod_ite]
      · intro p _
        exact Nat.cast_nonneg p
    _ ≤ B ^ N * (∏ p ∈ s, (p : ℝ)) ^ ε :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB hcard)
        (Real.rpow_nonneg (Finset.prod_nonneg (fun p _ => Nat.cast_nonneg p)) ε)

/-- The specialization used when all local labels divide the index,
so their product is at most that index. -/
theorem prod_le_index_subpower
    (f : ℕ → ℝ) (B ε : ℝ) (hB : 1 ≤ B) (hε : 0 < ε)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset ℕ) (q : ℝ),
      (∀ p ∈ s, 1 ≤ p) → (∏ p ∈ s, (p : ℝ)) ≤ q →
      (∏ p ∈ s, f p) ≤ C * q ^ ε := by
  obtain ⟨C, hC, hbound⟩ := prod_le_subpower_of_uniform_bound f B ε hB hε hf
  refine ⟨C, hC, fun s q hs hq => (hbound s hs).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Finset.prod_nonneg (fun p _ => Nat.cast_nonneg p)) hq hε.le) hC.le

end DukePrimeDegree

end OAI
