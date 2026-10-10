import Mathlib

namespace OAI

section
open scoped BigOperators


open scoped BigOperators
namespace ExactQuantumFactoring

/-- The telescoping estimate for any distinct integers at least two. -/
theorem prod_le_card_mul_pred_prod (s : Finset ℕ) (hs : ∀ p ∈ s, 2 ≤ p) :
    (∏ p ∈ s, p) ≤ (s.card + 1) * ∏ p ∈ s, (p - 1) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hmax ih =>
    have ha : a ∉ s := fun h => (lt_irrefl a) (hmax a h)
    have ha2 : 2 ≤ a := hs a (Finset.mem_insert_self _ _)
    have hs2 : ∀ p ∈ s, 2 ≤ p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hc : s.card + 2 ≤ a := by
      have hass : s ⊆ Finset.Ico 2 a := fun p hp => Finset.mem_Ico.mpr ⟨hs2 p hp, hmax p hp⟩
      have := Finset.card_le_card hass
      rw [Nat.card_Ico] at this
      omega
    have hstep : a * (s.card + 1) ≤ (s.card + 2) * (a - 1) := by
      have : a - 1 + 1 = a := by omega
      nlinarith
    simp only [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    calc
      a * ∏ p ∈ s, p ≤ a * ((s.card + 1) * ∏ p ∈ s, (p - 1)) :=
        Nat.mul_le_mul_left _ (ih hs2)
      _ ≤ (s.card + 1 + 1) * (a - 1) * ∏ p ∈ s, (p - 1) := by
        simpa [Nat.mul_assoc] using Nat.mul_le_mul_right (∏ p ∈ s, (p - 1)) hstep
      _ = (s.card + 1 + 1) * ((a - 1) * ∏ p ∈ s, (p - 1)) := by ring

/-- The number of distinct prime factors is less than a strict binary cutoff. -/
theorem primeFactors_card_lt {d n : ℕ} (hd : 0 < d) (hb : d < 2 ^ n) :
    d.primeFactors.card < n := by
  have hp : 2 ^ d.primeFactors.card ≤ ∏ p ∈ d.primeFactors, p := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod
      (fun prime hprime => (Nat.prime_of_mem_primeFactors hprime).two_le)
  have hp' : (∏ p ∈ d.primeFactors, p) ≤ d :=
    Nat.le_of_dvd hd (Nat.prod_primeFactors_dvd d)
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (hp.trans_lt (hp'.trans_lt hb))

/-- Integer form of (5.2), retaining the original global binary cutoff. -/
theorem le_succ_mul_totient {d n : ℕ} (hd : 0 < d) (hb : d < 2 ^ n) :
    d ≤ (n + 1) * Nat.totient d := by
  have hp := prod_le_card_mul_pred_prod d.primeFactors
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have hprodpos : 0 < ∏ p ∈ d.primeFactors, (p - 1) := by
    apply Finset.prod_pos
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hx := Nat.mul_le_mul_left (Nat.totient d) hp
  rw [Nat.totient_mul_prod_primeFactors] at hx
  have hbase : d ≤ (d.primeFactors.card + 1) * Nat.totient d := by
    apply Nat.le_of_mul_le_mul_right (c := ∏ p ∈ d.primeFactors, (p - 1)) _ hprodpos
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hx
  exact hbase.trans (Nat.mul_le_mul_right _ (by have := primeFactors_card_lt hd hb; omega))

/-- Real ratio version, ready for the exact transition-probability bound. -/
theorem totient_ratio_lower {d n : ℕ} (hd : 0 < d) (hb : d < 2 ^ n) :
    1 / ((n : ℝ) + 1) ≤ (Nat.totient d : ℝ) / d := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [div_le_div_iff₀ hn hd']
  norm_num only [one_mul]
  exact_mod_cast (le_succ_mul_totient hd hb).trans_eq (Nat.mul_comm _ _)

end ExactQuantumFactoring


end

end OAI
