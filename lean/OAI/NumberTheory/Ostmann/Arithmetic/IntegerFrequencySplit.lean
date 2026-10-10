import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace OAI

/-! # Separating positive and negative frequencies with a finite cutoff -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem integer_frequency_conjugate_split (F : ℤ → ℂ) (N : ℕ) (c : ℂ)
    (hzero : F 0 = 0) (hneg : ∀ n : ℕ, F (-(n : ℤ)) = c * conj (F n))
    (hcut : ∀ n : ℕ, N < n → F n = 0) :
    (∑' n : ℤ, F n) = (∑ n ∈ Finset.Icc 1 N, F n) +
      c * conj (∑ n ∈ Finset.Icc 1 N, F n) := by
  have hp (n : ℕ) (hn : n ∉ Finset.Icc 1 N) : F n = 0 := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    rcases hn with hn | hn
    · have he : n = 0 := by omega
      simpa only [he, Nat.cast_zero] using hzero
    · exact hcut n hn
  have hm (n : ℕ) (hn : n ∉ Finset.Icc 1 N) : F (-(n : ℤ)) = 0 := by
    rw [hneg, hp n hn, map_zero, mul_zero]
  have hps : Summable (fun n : ℕ => F n) := summable_of_ne_finset_zero hp
  have hms : Summable (fun n : ℕ => F (-(n : ℤ))) := summable_of_ne_finset_zero hm
  rw [hps.tsum_of_nat_of_neg hms, hzero, sub_zero, tsum_eq_sum hp, tsum_eq_sum hm]
  simp only [hneg, ← Finset.mul_sum, map_sum]

theorem integer_frequency_norm_le_twice (F : ℤ → ℂ) (N : ℕ) (c : ℂ)
    (hzero : F 0 = 0) (hneg : ∀ n : ℕ, F (-(n : ℤ)) = c * conj (F n))
    (hcut : ∀ n : ℕ, N < n → F n = 0) (hc : ‖c‖ ≤ 1) :
    ‖∑' n : ℤ, F n‖ ≤ 2 * ‖∑ n ∈ Finset.Icc 1 N, F n‖ := by
  rw [integer_frequency_conjugate_split F N c hzero hneg hcut]
  apply (norm_add_le _ _).trans
  rw [norm_mul, Complex.norm_conj]
  nlinarith [norm_nonneg (∑ n ∈ Finset.Icc 1 N, F n)]

end Ostmann

end OAI
