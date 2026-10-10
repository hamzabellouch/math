import OAI.NumberTheory.Ostmann.Preliminaries.SiftedEuler
import OAI.NumberTheory.Ostmann.Reuse.Mertens

namespace OAI

open Erdos970

namespace Ostmann.SiftedWeights
open Finset

def primeCutoff (N : ℕ) : Finset ℕ := (Ioc 0 N).filter Nat.Prime

def primeWindow (K N : ℕ) : Finset ℕ := primeCutoff N \ primeCutoff K

@[simp] theorem mem_primeWindow {K N p : ℕ} :
    p ∈ primeWindow K N ↔ p.Prime ∧ K < p ∧ p ≤ N := by
  simp only [primeWindow, primeCutoff, mem_sdiff, mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨⟨hp0, hpN⟩, hp⟩, hK⟩
    exact ⟨hp, lt_of_not_ge (fun h => hK ⟨⟨hp0, h⟩, hp⟩), hpN⟩
  · rintro ⟨hp, hK, hN⟩
    exact ⟨⟨⟨hp.pos, hN⟩, hp⟩, by omega⟩

theorem primeCutoff_mono {K N : ℕ} (h : K ≤ N) : primeCutoff K ⊆ primeCutoff N := by
  intro p hp
  simp only [primeCutoff, mem_filter, mem_Ioc] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.trans h⟩, hp.2⟩

theorem window_reciprocal_lower (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, max K 2 ≤ N →
      Real.log (Real.log (N : ℝ))-C ≤ ∑ p ∈ primeWindow K N, 1/(p : ℝ) := by
  obtain ⟨C, hC, hc⟩ := Ostmann.Reuse.primeReciprocal_lower_bound
  let E : ℝ := ∑ p ∈ primeCutoff K, 1/(p : ℝ)
  have hE : 0 ≤ E := Finset.sum_nonneg (fun p _ => by positivity)
  refine ⟨C+E, by positivity, ?_⟩
  intro N hN
  have hn2 : (2 : ℝ) ≤ N := by exact_mod_cast (le_max_right K 2).trans hN
  have hnK : K ≤ N := (le_max_left K 2).trans hN
  have hh := hc (N : ℝ) hn2
  simp only [Nat.floor_natCast] at hh
  change Real.log (Real.log (N : ℝ))-C ≤ ∑ p ∈ primeCutoff N, 1/(p : ℝ) at hh
  have hs := Finset.sum_sdiff (primeCutoff_mono hnK) (f := fun p : ℕ => 1/(p : ℝ))
  change (∑ p ∈ primeWindow K N, 1/(p : ℝ)) + E = _ at hs
  linarith

theorem window_log_upper (K N : ℕ) (hN : 1 ≤ N) :
    (∑ p ∈ primeWindow K N, Real.log (p : ℝ)/(p : ℝ)) ≤
      Real.log (N : ℝ)+(Real.log 4+4) := by
  have hh := Erdos970.Mertens.sum_log_prime_div_eq_log (x := (N : ℝ)) (by exact_mod_cast hN)
  simp only [Nat.floor_natCast] at hh
  have hupper := (abs_le.mp hh).2
  have hsub : primeWindow K N ⊆ primeCutoff N := Finset.sdiff_subset
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun p : ℕ => Real.log (p : ℝ)/(p : ℝ))
    (fun p hp _ => div_nonneg
      (Real.log_nonneg (by
        have hprime := (Finset.mem_filter.mp hp).2
        exact_mod_cast hprime.one_lt.le)) (by positivity))
  change (∑ p ∈ primeWindow K N, Real.log (p : ℝ)/(p : ℝ)) ≤
    ∑ p ∈ primeCutoff N, Real.log (p : ℝ)/(p : ℝ) at hsum
  change (∑ p ∈ primeCutoff N, Real.log (p : ℝ)/(p : ℝ))-Real.log (N : ℝ) ≤ _ at hupper
  linarith

theorem window_truncated_weight_lower (j K : ℕ) (hjK : j ≤ K) :
    ∃ c : ℝ, 0 < c ∧ ∀ N Q : ℕ, max K 2 ≤ N → 1 < Q →
      (j : ℝ)*(Real.log (N : ℝ)+(Real.log 4+4)) ≤ Real.log (Q : ℝ)/2 →
      c*(Real.log (N : ℝ))^j ≤
        ∑ t ∈ (primeWindow K N).powerset with (∏ p ∈ t, p) ≤ Q,
          ∏ p ∈ t, (j : ℝ)/((p : ℝ)-j) := by
  obtain ⟨C, hC, hc⟩ := window_reciprocal_lower K
  refine ⟨Real.exp (-(j : ℝ)*C)/2, by positivity, ?_⟩
  intro N Q hN hQ hmean
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hn2 : 2 ≤ N := (le_max_right K 2).trans hN
  have hP : ∀ p ∈ primeWindow K N, (j : ℝ) < p := by
    intro p hp
    exact_mod_cast lt_of_le_of_lt hjK (mem_primeWindow.mp hp).2.1
  have hm : (j : ℝ)*(∑ p ∈ primeWindow K N, Real.log p/(p : ℝ)) ≤
      Real.log (Q : ℝ)/2 :=
    (mul_le_mul_of_nonneg_left (window_log_upper K N (by omega)) hj).trans hmean
  have htr := truncated_euler_lower (primeWindow K N) hj hP hQ hm
  have hlo := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hc N hN) hj)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have he : Real.exp ((j : ℝ)*(Real.log (Real.log (N : ℝ))-C))/2 =
      (Real.exp (-(j : ℝ)*C)/2)*(Real.log (N : ℝ))^j := by
    rw [mul_sub, Real.exp_sub, Real.exp_nat_mul, Real.exp_log hlog,
      show -(j : ℝ)*C = -((j : ℝ)*C) by ring, Real.exp_neg]
    ring
  rw [← he]
  exact (div_le_div_of_nonneg_right hlo (by norm_num)).trans htr

end Ostmann.SiftedWeights

end OAI
