import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.PrimeIntervals

lemma card_primes_le (s : Finset ℕ) (y : ℝ) (hy : 0 ≤ y)
    (hs : ∀ p ∈ s, p.Prime ∧ (p : ℝ) ≤ y) :
    (s.card : ℝ) ≤ Nat.primeCounting ⌊y⌋₊ := by
  have hsub : s ⊆ (⌊y⌋₊ + 1).primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow]
    exact ⟨Nat.lt_succ_iff.mpr ((Nat.le_floor_iff hy).mpr (hs p hp).2), (hs p hp).1⟩
  have hc := card_le_card hsub
  rw [Nat.primesBelow_card_eq_primeCounting'] at hc
  exact_mod_cast hc

lemma reciprocal_interval_bound {s : Finset ℕ} {τ x L C : ℝ}
    (hτ : 0 < τ) (hL : 0 < L) (hC : 0 ≤ C)
    (hs : ∀ p ∈ s, p.Prime ∧ Real.exp L < (p : ℝ) ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ τ*x)
    (hcount : (Nat.primeCounting ⌊τ*x⌋₊ : ℝ) ≤ C * (τ*x) / Real.log (τ*x)) :
    ∑ p ∈ s, (p : ℝ)⁻¹ ≤ C * τ / L := by
  by_cases hs0 : s.Nonempty
  · obtain ⟨p,hp⟩ := hs0
    have htx : Real.exp L < τ*x := (hs p hp).2.1.trans_le (hs p hp).2.2.2
    have htxpos : 0 < τ*x := (Real.exp_pos _).trans htx
    have hx : 0 < x := pos_of_mul_pos_right htxpos hτ.le
    have hlog : L < Real.log (τ*x) := by simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) htx
    have hk := card_primes_le s (τ*x) htxpos.le (fun p hp => ⟨(hs p hp).1,(hs p hp).2.2.2⟩)
    calc
      _ ≤ ∑ _p ∈ s, x⁻¹ := sum_le_sum (fun p hp => inv_anti₀ hx (hs p hp).2.2.1.le)
      _ = (s.card : ℝ) / x := by simp [div_eq_mul_inv]
      _ ≤ (Nat.primeCounting ⌊τ*x⌋₊ : ℝ) / x := div_le_div_of_nonneg_right hk hx.le
      _ ≤ (C * (τ*x) / Real.log (τ*x)) / x := div_le_div_of_nonneg_right hcount hx.le
      _ = C * τ / Real.log (τ*x) := by field_simp
      _ ≤ C * τ / L := div_le_div_of_nonneg_left (mul_nonneg hC hτ.le) hL hlog.le
  · have : s = ∅ := not_nonempty_iff_eq_empty.mp hs0
    simp only [this,sum_empty]
    positivity

theorem uniform_prime_bin (r τ : ℝ) (hr : 0 < r) (hτ : 0 < τ) :
    ∀ᶠ B : ℝ in atTop, ∀ (x : ℝ) (s : Finset ℕ),
      (∀ p ∈ s, p.Prime ∧ Real.exp (B^r) < (p : ℝ) ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ τ*x) →
      ∑ p ∈ s, (p : ℝ)⁻¹ ≤ ((Real.log 4 + 1) * τ) / B^r := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp (Chebyshev.eventually_primeCounting_le (by norm_num : (0:ℝ)<1))
  have hlim := Real.tendsto_exp_atTop.comp (tendsto_rpow_atTop hr)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlim.eventually (eventually_ge_atTop M)] with B hB hBM
  intro x s hs
  by_cases hsn : s.Nonempty
  · obtain ⟨p,hp⟩ := hsn
    have htx : M ≤ τ*x := hBM.trans ((hs p hp).2.1.le.trans (hs p hp).2.2.2)
    exact reciprocal_interval_bound hτ (Real.rpow_pos_of_pos (by linarith) _)
      (by positivity) hs (hM _ htx)
  · have : s=∅ := not_nonempty_iff_eq_empty.mp hsn
    simp only [this,sum_empty]
    positivity

end OrdinaryCorrelations.PrimeIntervals

end

end OAI
