import Mathlib.Data.Nat.GCD.BigOperators
import OAI.NumberTheory.Ostmann.Supply.PrimeSubsetProducts
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityPrimeBlock

namespace OAI

/-! # Constructing the original small-prime amplification modulus -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def amplificationPrimeCount (T : ℝ) (z : ℕ) : ℕ :=
  ⌊T / (50 * Real.log (2 * (z : ℝ)))⌋₊

theorem primeSet_prod_le_exp (Q : Finset ℕ) (z : ℕ) (T : ℝ)
    (hz : 0 < z) (hQ : ∀ p ∈ Q, p ≤ 2 * z)
    (hlog : (Q.card : ℝ) * Real.log (2 * (z : ℝ)) ≤ T) :
    (Q.toList.prod : ℝ) ≤ Real.exp T := by
  have hp := Finset.prod_le_pow_card Q (fun p : ℕ => p) (2 * z) hQ
  have hpR : (Q.toList.prod : ℝ) ≤ (2 * (z : ℝ)) ^ Q.card := by
    have hh : Q.toList.prod = ∏ p ∈ Q, p := by simp
    rw [hh]
    exact_mod_cast hp
  apply hpR.trans
  have hzR : 0 < 2 * (z : ℝ) := by positivity
  rw [← Real.exp_log hzR, ← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr hlog

theorem two_le_primeSet_prod (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (hne : Q.Nonempty) :
    2 ≤ Q.toList.prod := by
  have hp := Finset.pow_card_le_prod Q (fun p : ℕ => p) 2 (fun p hp => (hQ p hp).two_le)
  have he : Q.toList.prod = ∏ p ∈ Q, p := by simp
  rw [he]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) hne.card_pos).trans hp

theorem exists_amplification_prime_subset (P : Finset ℕ) (z : ℕ) (T : ℝ)
    (hz : 2 ≤ z) (hT : 0 ≤ T) (hP : ∀ p ∈ P, p.Prime)
    (hrange : ∀ p ∈ P, p < 2 * z)
    (hcount : amplificationPrimeCount T z ≤ P.card)
    (hK : 1 ≤ amplificationPrimeCount T z) :
    ∃ Q ⊆ P, Q.card = amplificationPrimeCount T z ∧
      (∀ p ∈ Q, p.Prime) ∧ 2 ≤ Q.toList.prod ∧
      (Q.toList.prod : ℝ) ≤ Real.exp (T / 50) := by
  obtain ⟨Q, hQP, hcard⟩ := Finset.exists_subset_card_eq hcount
  have hQ : ∀ p ∈ Q, p.Prime := fun p hp => hP p (hQP hp)
  have hne : Q.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨Q, hQP, hcard, hQ, two_le_primeSet_prod Q hQ hne, ?_⟩
  apply primeSet_prod_le_exp Q z (T / 50) (by omega)
    (fun p hp => (hrange p (hQP hp)).le)
  have hlog : 0 < Real.log (2 * (z : ℝ)) := Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * z))
  have hfloor : (amplificationPrimeCount T z : ℝ) ≤ T / (50 * Real.log (2 * (z : ℝ))) :=
    Nat.floor_le (div_nonneg hT (by positivity))
  rw [hcard]
  have hh := (le_div_iff₀ (show 0 < 50 * Real.log (2 * (z : ℝ)) by positivity)).mp hfloor
  linarith

theorem separated_prime_products_coprime (Q P : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (hP : ∀ p ∈ P, p.Prime)
    (hsep : ∀ p ∈ Q, ∀ q ∈ P, p < q) (k M : ℕ) (hM : M ∈ primeSubsetProducts P k) :
    Q.toList.prod.Coprime M := by
  obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hM
  have hRP := (Finset.mem_powersetCard.mp hR).1
  have he : Q.toList.prod = ∏ p ∈ Q, p := by simp
  rw [he]
  apply Nat.Coprime.prod_left
  intro p hp
  apply Nat.Coprime.prod_right
  intro q hq
  exact (Nat.coprime_primes (hQ p hp) (hP q (hRP hq))).mpr (ne_of_lt (hsep p hp q (hRP hq)))

end Ostmann

end OAI
