import Mathlib.Data.Nat.Log
import OAI.NumberTheory.Ostmann.Arithmetic.ResiduePopulationCount
import OAI.NumberTheory.Ostmann.Construction.HarmonicWordPriors
import OAI.NumberTheory.Ostmann.Construction.FiniteCellPrior

namespace OAI

/-! # Coarse residue domination for the original harmonic prime priors

Only an upper bound is needed here. Dyadic interval counts give it without
any distribution theorem for primes, including at the boundary of a word bin.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem harmonic_residue_block_le (S : Finset ℕ) (q N : ℕ)
    (hq : 0 < q) (hN : q ≤ N)
    (hrange : ∀ n ∈ S, N ≤ n ∧ n ≤ 2 * N)
    (hcongr : ∀ a ∈ S, ∀ b ∈ S, a ≡ b [MOD q]) :
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤ 3 / q := by
  have hNpos : 0 < N := lt_of_lt_of_le hq hN
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hcard := nat_progression_population_card_le S q N hq
    (fun a ha b hb => by
      have ha' := hrange a ha
      have hb' := hrange b hb
      rcases le_total a b with hab | hba
      · rw [Nat.dist_eq_sub_of_le hab]; omega
      · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hba]; omega) hcongr
  have hi : (N : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hqreal (show (q : ℝ) ≤ (N : ℝ) by exact_mod_cast hN)
  calc
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤ ∑ _n ∈ S, (N : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      simpa only [one_div] using one_div_le_one_div_of_le hNreal
        (show (N : ℝ) ≤ (n : ℝ) by exact_mod_cast (hrange n hn).1)
    _ = (S.card : ℝ) * (N : ℝ)⁻¹ := by simp
    _ ≤ ((N : ℝ) / q + 2) * (N : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (q : ℝ)⁻¹ + 2 * (N : ℝ)⁻¹ := by
      field_simp
    _ ≤ 3 / q := by simp only [div_eq_mul_inv]; linarith

/-- The number of dyadic blocks, rather than the length of the prime range,
controls the harmonic mass of a residue class. -/
theorem harmonic_residue_dyadic_le (S : Finset ℕ) (q h J : ℕ)
    (hq : 0 < q) (hsmall : q ≤ 2 ^ h)
    (hrange : ∀ n ∈ S, 2 ^ h ≤ n ∧ n < 2 ^ (h + J))
    (hcongr : ∀ a ∈ S, ∀ b ∈ S, a ≡ b [MOD q]) :
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤ 3 * J / q := by
  let block (j n : ℕ) : Prop := 2 ^ (h + j) ≤ n ∧ n < 2 ^ (h + j + 1)
  have hcover (n : ℕ) (hn : n ∈ S) : ∃ j ∈ Finset.range J, block j n := by
    have hnpos : n ≠ 0 := by have := (hrange n hn).1; have := Nat.two_pow_pos h; omega
    have hlo : h ≤ Nat.log 2 n :=
      (Nat.le_log_iff_pow_le (by norm_num) hnpos).mpr (hrange n hn).1
    have hhi : Nat.log 2 n < h + J :=
      (Nat.log_lt_iff_lt_pow (by norm_num) hnpos).mpr (hrange n hn).2
    refine ⟨Nat.log 2 n - h, Finset.mem_range.mpr (by omega), ?_⟩
    have he : h + (Nat.log 2 n - h) = Nat.log 2 n := by omega
    dsimp [block]
    rw [he]
    exact ⟨Nat.pow_log_le_self 2 hnpos, Nat.lt_pow_succ_log_self (by norm_num) n⟩
  calc
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤
        ∑ n ∈ S, ∑ j ∈ Finset.range J, if block j n then (n : ℝ)⁻¹ else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨j, hj, hb⟩ := hcover n hn
      have hs := Finset.single_le_sum
        (f := fun j => if block j n then (n : ℝ)⁻¹ else 0)
        (fun j _ => by split_ifs <;> positivity) hj
      simpa only [ite_eq_left hb] using hs
    _ = ∑ j ∈ Finset.range J, ∑ n ∈ S.filter (block j), (n : ℝ)⁻¹ := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ ≤ ∑ _j ∈ Finset.range J, 3 / (q : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      apply harmonic_residue_block_le _ q (2 ^ (h + j)) hq
      · exact hsmall.trans (Nat.pow_le_pow_right (by omega) (by omega))
      · intro n hn
        have hb := (Finset.mem_filter.mp hn).2
        exact ⟨hb.1, by have := hb.2; dsimp [block] at *; rw [pow_succ] at this; omega⟩
      · intro a ha b hb
        exact hcongr a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
    _ = 3 * J / q := by simp; ring

/-- Exact harmonic priors on arbitrary prime subsets obey the same bound.
No primality or interval closure of the selected subset is needed. -/
theorem primeSubsetPrior_residue_le (P S : Finset ℕ) (q h J : ℕ)
    (hq : 0 < q) (hsmall : q ≤ 2 ^ h)
    (hrange : ∀ n ∈ S, 2 ^ h ≤ n ∧ n < 2 ^ (h + J)) (a : ZMod q) :
    cellPrior (primeSubsetPrior P S) (fun p => ((p : ℕ) : ZMod q)) a ≤
      (∑ n ∈ S, (n : ℝ)⁻¹)⁻¹ * (3 * J / q) := by
  classical
  let T := P.filter (fun p => p ∈ S ∧ (p : ZMod q) = a)
  have hmass : 0 ≤ (∑ n ∈ S, (n : ℝ)⁻¹)⁻¹ := by positivity
  have hT := harmonic_residue_dyadic_le T q h J hq hsmall
    (fun n hn => hrange n (Finset.mem_filter.mp hn).2.1)
    (fun b hb c hc => (ZMod.natCast_eq_natCast_iff b c q).mp
      ((Finset.mem_filter.mp hb).2.2.trans (Finset.mem_filter.mp hc).2.2.symm))
  have heq : cellPrior (primeSubsetPrior P S) (fun p => ((p : ℕ) : ZMod q)) a =
      (∑ n ∈ S, (n : ℝ)⁻¹)⁻¹ * ∑ n ∈ T, (n : ℝ)⁻¹ := by
    let f (p : ℕ) : ℝ := if (p : ZMod q) = a then
      if p ∈ S then (p : ℝ)⁻¹ / (∑ n ∈ S, (n : ℝ)⁻¹) else 0 else 0
    have hf : cellPrior (primeSubsetPrior P S) (fun p => ((p : ℕ) : ZMod q)) a =
        ∑ p : P, f p := by
      unfold cellPrior
      apply Finset.sum_congr rfl
      intro p _
      dsimp [f, primeSubsetPrior]
      split_ifs <;> rfl
    rw [hf, Finset.sum_coe_sort P f]
    dsimp only [f]
    simp only [T, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hpa : (p : ZMod q) = a <;> by_cases hpS : p ∈ S <;>
      simp [hpa, hpS, div_eq_mul_inv, mul_comm]
  rw [heq]
  exact mul_le_mul_of_nonneg_left hT hmass

end Ostmann

end OAI
