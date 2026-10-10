import OAI.NumberTheory.TwoPointCorrelations.MRTMultiplicativeReduction
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

/-! A finite-Euler-product criterion for the absolutely summable correction
in the general-multiplicative reduction.  The criterion is proved from local
prime-power sums, not used as a new analytic input. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical BigOperators

theorem mrt_summable_of_local_euler_bound (a : ℕ → ℝ)
    (ha0 : a 0 = 0) (ha1 : a 1 = 1) (ha : ∀ n, 0 ≤ a n)
    (hmul : ∀ {m n}, m.Coprime n → a (m * n) = a m * a n)
    (hloc : ∀ p : ℕ, p.Prime → Summable (fun k : ℕ => a (p ^ k)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ p : ℕ, p.Prime →
      (∑' k : ℕ, a (p ^ k)) ≤ Real.exp (C * (p : ℝ) ^ (-(3 / 2 : ℝ)))) :
    Summable a ∧
      (∑' n : ℕ, a n) ≤ Real.exp (C * ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
  have hpseries : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
    exact Real.summable_nat_rpow.mpr (by norm_num)
  have hprefix (N : ℕ) :
      (∑ n ∈ range N, a n) ≤ Real.exp (C * ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
    have hlocnorm : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ => ‖a (p ^ k)‖) := by
      intro p hp
      simpa only [Real.norm_eq_abs, abs_of_nonneg (ha _)] using hloc p hp
    obtain ⟨_, hprod⟩ :=
      EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum ha1 hmul hlocnorm N
    have hi := hasSum_subtype_iff_indicator.mp hprod
    have hsum : (∑ n ∈ range N, a n) =
        ∑ n ∈ range N, (Nat.smoothNumbers N).indicator a n := by
      apply sum_congr rfl
      intro n hn
      by_cases hn0 : n = 0
      · simp [hn0, ha0, Set.indicator_apply]
      · exact (Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt
          (Nat.pos_of_ne_zero hn0) (mem_range.mp hn)) a).symm
    rw [hsum]
    calc
      _ ≤ ∏ p ∈ N.primesBelow, ∑' k : ℕ, a (p ^ k) := by
        rw [← hi.tsum_eq]
        apply hi.summable.sum_le_tsum
        intro n _
        exact Set.indicator_nonneg (fun n _ => ha n) n
      _ ≤ ∏ p ∈ N.primesBelow, Real.exp (C * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
        apply prod_le_prod₀
        · intro p _
          exact tsum_nonneg (fun _ => ha _)
        · intro p hp
          exact hbound p (Nat.prime_of_mem_primesBelow hp)
      _ = Real.exp (C * ∑ p ∈ N.primesBelow, (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
        rw [mul_sum, Real.exp_sum]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ hC
        exact hpseries.sum_le_tsum _ (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact ⟨summable_of_sum_range_le ha hprefix, Real.tsum_le_of_sum_range_le ha hprefix⟩

end TwoPointCorrelations

end OAI
