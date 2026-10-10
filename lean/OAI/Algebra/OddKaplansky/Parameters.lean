import Mathlib

namespace OAI

section
namespace OddKaplansky

@[irreducible] def sourceM : ℕ := Nat.choose 1200 600
@[irreducible] def sourcePrime : ℕ := Nat.minFac ((Nat.factorial sourceM)^2 + 1)

lemma sourceM_large : 1200 ≤ sourceM := by
  have h := Nat.choose_le_middle 1 1200
  rw [Nat.choose_one_right, show 1200 / 2 = 600 from rfl] at h
  unfold sourceM
  exact h

lemma sourcePrime_prime : sourcePrime.Prime := by
  unfold sourcePrime
  apply Nat.minFac_prime
  have := Nat.factorial_pos sourceM
  have := pow_pos this 2
  omega

lemma sourcePrime_dvd : sourcePrime ∣ (Nat.factorial sourceM)^2 + 1 :=
  by unfold sourcePrime; exact Nat.minFac_dvd _

lemma sourcePrime_gt : sourceM < sourcePrime := by
  by_contra h
  have hd := Nat.dvd_factorial sourcePrime_prime.pos (Nat.le_of_not_gt h)
  have hsq : sourcePrime ∣ (Nat.factorial sourceM)^2 :=
    dvd_pow hd (by decide : 2 ≠ 0)
  have : sourcePrime ∣ 1 := (Nat.dvd_add_iff_right hsq).mpr sourcePrime_dvd
  exact sourcePrime_prime.not_dvd_one this

lemma sourcePrime_odd : Odd sourcePrime :=
  sourcePrime_prime.odd_of_ne_two (by have := sourcePrime_gt; have := sourceM_large; omega)

lemma sourcePrime_minimal (n : ℕ) (hn : 1 < n)
    (hd : n ∣ (Nat.factorial sourceM)^2 + 1) : sourcePrime ≤ n :=
  by unfold sourcePrime; exact Nat.minFac_le_of_dvd hn hd

instance sourcePrime_fact : Fact sourcePrime.Prime := ⟨sourcePrime_prime⟩

lemma neg_one_isSquare_of_dvd (p n : ℕ) [Fact p.Prime] (h : p ∣ n^2+1) :
    IsSquare (-1 : ZMod p) := by
  refine ⟨(n : ZMod p), ?_⟩
  have hz : (((n^2+1 : ℕ) : ZMod p)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr h
  push_cast at hz
  linear_combination -hz

lemma neg_one_isSquare : IsSquare (-1 : ZMod sourcePrime) :=
  neg_one_isSquare_of_dvd sourcePrime (Nat.factorial sourceM) sourcePrime_dvd

end OddKaplansky

end

end OAI
