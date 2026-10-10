import OAI.NumberTheory.TwoPoint.Bounds.PrimeModulusDefect
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Divergent reciprocal prime-modulus defect forces vanishing ordinary
mean modulus, using only the finite p² CRT majorants. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical Topology

lemma Multiplicative.eq_zero_of_one_ne {f : ℕ → ℂ}
    (hf : Multiplicative f) (h1 : f 1 ≠ 1) (n : ℕ) (hn : 0 < n) : f n = 0 := by
  have he : f n = f 1 * f n := by
    simpa only [one_mul] using hf 1 n (by omega) hn (Nat.coprime_one_left n)
  have hm : (1 - f 1) * f n = 0 := by linear_combination he
  rcases mul_eq_zero.mp hm with h | h
  · exact False.elim (h1 (sub_eq_zero.mp h).symm)
  · exact h

lemma modulus_mean_nonneg (f : ℕ → ℂ) (N : ℕ) :
    0 ≤ (∑ n ∈ range N, ‖f (n + 1)‖) / (N : ℝ) :=
  div_nonneg (sum_nonneg (fun _ _ => norm_nonneg _)) (Nat.cast_nonneg N)

theorem mean_modulus_zero_of_not_summable_prime_defect {f : ℕ → ℂ}
    (hfm : Multiplicative f) (hf : OneBounded f)
    (hns : ¬Summable (primeModulusDefect f)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, ‖f (n + 1)‖) / (N : ℝ))
      atTop (𝓝 0) := by
  by_cases hf1 : f 1 = 1
  · have hsum := (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (primeModulusDefect_nonneg hf)).mp hns
    apply Metric.tendsto_atTop.2
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    obtain ⟨M, hM⟩ := (hsum.eventually
      (eventually_ge_atTop (-2 * Real.log (ε / 2)))).exists
    let P := (range M).filter Nat.Prime
    have hP : ∀ p ∈ P, p.Prime := fun p hp => (mem_filter.mp hp).2
    have hpsum : (∑ p ∈ P, primeModulusDefect f p) =
        ∑ p ∈ range M, primeModulusDefect f p := by
      rw [sum_filter]
      apply sum_congr rfl
      intro p _
      by_cases hp : p.Prime <;> simp [primeModulusDefect, hp]
    have hprod : (∏ p ∈ P, (1 - (1 - ‖f p‖) *
        (1 / (p : ℝ) - 1 / (p : ℝ) ^ 2))) ≤ ε / 2 := by
      apply (prime_square_defect_product_le_exp hf P hP).trans
      have hh : -(∑ p ∈ P, primeModulusDefect f p) / 2 ≤ Real.log (ε / 2) := by
        rw [hpsum]
        linarith
      exact (Real.exp_le_exp.mpr hh).trans_eq (Real.exp_log hε2)
    let Q := ∏ p ∈ P, (p : ℝ) ^ 2
    have htail : Tendsto (fun N : ℕ => Q / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat Q
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
      ((htail.eventually (gt_mem_nhds hε2)).and (eventually_ge_atTop 1))
    refine ⟨N₀, ?_⟩
    intro N hN
    obtain ⟨hsmall, hN1⟩ := hN₀ N hN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (modulus_mean_nonneg f N)]
    have hbound := primeDefectMajorant_crt_bound hfm hf1 hf P hP N (by omega)
    change _ ≤ _ + Q / N at hbound
    linarith
  · have he : (fun N : ℕ => (∑ n ∈ range N, ‖f (n + 1)‖) / (N : ℝ)) =
        fun _ => 0 := by
      funext N
      have hz : (∑ n ∈ range N, ‖f (n + 1)‖) = 0 := by
        apply sum_eq_zero
        intro n _
        rw [hfm.eq_zero_of_one_ne hf1 (n + 1) (by omega), norm_zero]
      rw [hz, zero_div]
    rw [he]
    exact tendsto_const_nhds

end TwoPointCorrelations

end OAI
