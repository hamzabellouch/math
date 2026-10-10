import OAI.NumberTheory.Ostmann.Preliminaries.FixedShiftResidues
import OAI.NumberTheory.Ostmann.Supply.PrimeSetSupportSieve

namespace OAI

/-! # The fixed-shift counting sieve with its actual local weights -/

namespace Ostmann

open scoped Classical BigOperators

 theorem finiteShiftAllowed_weight (B : Finset ℕ) (p : ℕ) [NeZero p]
    (hB : ∀ b ∈ B, b < p) (hcard : B.card < p) :
    (finiteShiftAllowed B p).Nonempty ∧
      (p : ℝ) / (finiteShiftAllowed B p).card - 1 =
        (B.card : ℝ) / ((p : ℝ) - B.card) := by
  have hsum := finiteShiftAllowed_card B p hB
  have hpos : 0 < (finiteShiftAllowed B p).card := by omega
  have hposR : (0 : ℝ) < (finiteShiftAllowed B p).card := by exact_mod_cast hpos
  have hsumR : ((finiteShiftAllowed B p).card : ℝ) + B.card = p := by exact_mod_cast hsum
  have hd : (0 : ℝ) < (p : ℝ) - B.card := by linarith
  refine ⟨Finset.card_pos.mp hpos, ?_⟩
  field_simp
  nlinarith

 theorem fixed_shift_sieve_bound {M Q : ℕ} (B P : Finset ℕ)
    (hM : 1 ≤ M) (hQ : 1 ≤ Q) (A : Finset (Fin M)) (hA : A.Nonempty)
    (hP : ∀ p ∈ P, p.Prime) (hPQ : ∀ p ∈ P, p ≤ Q) (hB : ∀ p ∈ P, ∀ b ∈ B, b < p)
    (hcard : ∀ p ∈ P, B.card < p)
    (hlarge : ∀ a ∈ A, Q < a.val)
    (hprime : ∀ a ∈ A, ∀ b ∈ B, (a.val + b).Prime) :
    (∑ U ∈ boundedSieveSubsets P Q,
      ∏ p ∈ U, (B.card : ℝ) / ((p : ℝ) - B.card)) ≤
        ((M : ℝ) + (Q : ℝ) ^ 2) / A.card := by
  have hS (p : ℕ) (hp : p ∈ P) : (finiteShiftAllowed B p).Nonempty := by
    let : NeZero p := ⟨(hP p hp).ne_zero⟩
    exact (finiteShiftAllowed_weight B p (hB p hp)
      (hcard p hp)).1
  have h := prime_set_support_sieve P hP
    (finiteShiftAllowed B) hS hQ hM A hA 0 (by
      intro a ha p hp
      let : NeZero p := ⟨(hP p hp).ne_zero⟩
      have hpQ := hPQ p hp
      simpa only [zero_add, Int.cast_natCast] using
        finiteShiftAllowed_mem_of_prime B p a.val (hP p hp)
          (lt_of_le_of_lt hpQ (hlarge a ha)) (hprime a ha))
  convert h using 1
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.prod_congr rfl
  intro p hp
  have hpP := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1 hp
  let : NeZero p := ⟨(hP p hpP).ne_zero⟩
  exact (finiteShiftAllowed_weight B p (hB p hpP) (hcard p hpP)).2.symm

end Ostmann

end OAI
