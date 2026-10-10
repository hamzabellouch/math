import OAI.NumberTheory.JointDickman.Amplification.BinStateExtraction
import OAI.NumberTheory.JointDickman.Arithmetic.DistinctBinDistribution

namespace OAI

/-! # Generating functions are unchanged by discarding repeated large primes -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem distinctBinCount_le_binCount (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime)
    {n : ℕ} (hn : n ≠ 0) : distinctBinCount E n ≤ binCount E n := by
  classical
  have he : distinctBinCount E n = ∑ p ∈ E, if p ∣ n then 1 else 0 := by
    simp [distinctBinCount]
  rw [he, binCount]
  apply sum_le_sum
  intro p hp
  split_ifs with hpn
  · exact (hE p hp).factorization_pos_of_dvd hn hpn
  · exact Nat.zero_le _

theorem distinctBinVector_val {J : ℕ} (hJ : 0 < J) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ A*x →
      ∀ i : Fin (J-1), (distinctBinVector J x n i).val =
        distinctBinCount (primeBin x J (i.val+1)) n := by
  filter_upwards [primeBin_count_eventually_le J hJ A, eventually_ge_atTop (0 : ℝ)] with x hx hx0 n hn hnx i
  apply min_eq_left
  exact (distinctBinCount_le_binCount _
    (fun p hp => ((mem_primeBin_iff hx0 _ _ _).mp hp).1) (by omega)).trans
    (hx _ (by omega) n hn hnx)

noncomputable def distinctBinGeneratingAverage (J : ℕ) (z : Fin (J-1) → ℝ) (A x : ℝ) : ℝ :=
  (∑ n ∈ Ioc 0 ⌊A*x⌋₊, ∏ i, z i^(distinctBinVector J x n i).val)/(A*x)

theorem binStateGeneratingAverage_states (J : ℕ) (z : Fin (J-1) → ℝ) (A x : ℝ) :
    binStateGeneratingAverage J z A x =
      ∑ r : BinCountState J, binStateDensity J A x r * ∏ i, z i^(r i).val := by
  rw [binStateGeneratingAverage, finite_state_sum (Ioc 0 ⌊A*x⌋₊) (canonicalBinVector J x)
    (fun r : BinCountState J => ∏ i, z i^(r i).val)]
  simp only [sum_div, binStateDensity]
  apply sum_congr rfl
  intros
  ring

theorem distinctBinGeneratingAverage_states (J : ℕ) (z : Fin (J-1) → ℝ) (A x : ℝ) :
    distinctBinGeneratingAverage J z A x =
      ∑ r : BinCountState J, distinctBinStateDensity J A x r * ∏ i, z i^(r i).val := by
  rw [distinctBinGeneratingAverage, finite_state_sum (Ioc 0 ⌊A*x⌋₊) (distinctBinVector J x)
    (fun r : BinCountState J => ∏ i, z i^(r i).val)]
  simp only [sum_div, distinctBinStateDensity]
  apply sum_congr rfl
  intros
  ring

theorem binGenerating_sub_distinct_tendsto {J : ℕ} (hJ : 0 < J)
    (z : Fin (J-1) → ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x => binStateGeneratingAverage J z A x - distinctBinGeneratingAverage J z A x)
      atTop (𝓝 0) := by
  have ht := tendsto_finsetSum univ (fun r _ =>
    (binStateDensity_sub_distinct_tendsto hJ hA r).mul_const (∏ i, z i^(r i).val))
  simpa only [binStateGeneratingAverage_states, distinctBinGeneratingAverage_states,
    ← sum_sub_distrib, ← sub_mul, zero_mul, sum_const_zero] using ht

end JointDickman

end OAI
