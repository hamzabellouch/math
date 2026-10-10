import OAI.NumberTheory.Ostmann.Dirichlet.PrimeSeriesDefinitions
import OAI.NumberTheory.Ostmann.Preliminaries.PrimeSums

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Dirichlet
open Ostmann.Preliminaries
open scoped BigOperators

lemma ordinaryPrimeSeriesTerm_le_log_div {σ : ℝ} (hσ : 1 ≤ σ) {p : ℕ} (hp : p.Prime) :
    ordinaryPrimeSeriesTerm σ p ≤ Real.log p / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hpow : (p : ℝ) ≤ (p : ℝ) ^ σ := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hp1 hσ
  simp only [ordinaryPrimeSeriesTerm, hp, ite_true]
  exact div_le_div_of_nonneg_left (Real.log_nonneg hp1) hp0 hpow

theorem sum_prime_divisor_log_weight_le (P : Finset ℕ) (M : ℕ) (hM : 1 ≤ M)
    (hprime : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, p ∣ M)
    {R : ℝ} (hR : 1 ≤ R) :
    (∑ p ∈ P, Real.log p / p) ≤
      Real.log R + (Real.log 4 + 4) + Real.log M / R := by
  classical
  let S : Finset ℕ := P.filter (fun (p : ℕ) => (p : ℝ) ≤ R)
  let U : Finset ℕ := P.filter (fun (p : ℕ) => ¬(p : ℝ) ≤ R)
  have hR0 : 0 < R := by linarith
  have hsmall : S ⊆ (⌊R⌋₊).primesLE := by
    intro p hp
    have hm := Finset.mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor hm.2, hprime p hm.1⟩
  have hs : (∑ p ∈ S, Real.log p / p) ≤ Real.log R + (Real.log 4 + 4) := by
    have hsum : (∑ p ∈ S, Real.log p / p) ≤
        ∑ p ∈ (⌊R⌋₊).primesLE, Real.log p / p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsmall
      intro p hp _
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le))
        (Nat.cast_nonneg p)
    have hf : 1 ≤ ⌊R⌋₊ := (Nat.one_le_floor_iff _).mpr hR
    have hm := (abs_le.mp (mertens_prime_sum ⌊R⌋₊ hf)).2
    have hlog : Real.log (⌊R⌋₊ : ℝ) ≤ Real.log R :=
      Real.log_le_log (by exact_mod_cast hf) (Nat.floor_le hR0.le)
    linarith
  have hu : (∑ p ∈ U, Real.log p / p) ≤ Real.log M / R := by
    calc
      _ ≤ ∑ p ∈ U, Real.log p / R := by
        apply Finset.sum_le_sum
        intro p hp
        have hm := Finset.mem_filter.mp hp
        have hpp := hprime p hm.1
        exact div_le_div_of_nonneg_left
          (Real.log_nonneg (by exact_mod_cast hpp.one_le)) hR0 (le_of_not_ge hm.2)
      _ = (∑ p ∈ U, Real.log p) / R := by rw [Finset.sum_div]
      _ ≤ Real.log M / R := by
        apply div_le_div_of_nonneg_right _ hR0.le
        exact sum_log_prime_divisors_le U M (by omega)
          (fun p hp => hprime p (Finset.mem_filter.mp hp).1)
          (fun p hp => hdiv p (Finset.mem_filter.mp hp).1)
  have hsplit := Finset.sum_filter_add_sum_filter_not P (fun p : ℕ => (p : ℝ) ≤ R)
    (fun p : ℕ => Real.log p / p)
  change (∑ p ∈ S, Real.log p / p) + (∑ p ∈ U, Real.log p / p) = _ at hsplit
  linarith

theorem sum_prime_divisor_ordinary_le (P : Finset ℕ) (M : ℕ) (hM : 1 ≤ M)
    (hprime : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, p ∣ M)
    {R σ : ℝ} (hR : 1 ≤ R) (hσ : 1 ≤ σ) :
    (∑ p ∈ P, ordinaryPrimeSeriesTerm σ p) ≤
      Real.log R + (Real.log 4 + 4) + Real.log M / R := by
  exact (Finset.sum_le_sum (fun p hp => ordinaryPrimeSeriesTerm_le_log_div hσ (hprime p hp))).trans
    (sum_prime_divisor_log_weight_le P M hM hprime hdiv hR)

end Ostmann.Dirichlet

end

end OAI
