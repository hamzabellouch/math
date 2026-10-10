import OAI.NumberTheory.Ostmann.Arithmetic.HistorySupportDescentIntegrality

namespace OAI

namespace Ostmann.Arithmetic.HistorySupportDescent

theorem compensation_square_not_dvd {u : List ℕ} (hu : u.Pairwise Nat.Coprime)
    {b : ℕ} (hb : b ∈ u) (hbprime : Nat.Prime b) :
    ¬ (b : ℤ) * b ∣ (u.prod : ℤ) := by
  have he := List.perm_cons_erase hb
  have hpw := (he.pairwise_iff Nat.Coprime.symm).mp hu
  have hc : Nat.Coprime b (u.erase b).prod :=
    Nat.coprime_list_prod_right_iff.mpr (List.pairwise_cons.mp hpw).1
  have hprod : u.prod = b * (u.erase b).prod := he.prod_eq
  intro hd
  rw [hprod,Nat.cast_mul] at hd
  have hb0 : (b : ℤ) ≠ 0 := by exact_mod_cast hbprime.ne_zero
  have hd' : (b : ℤ) ∣ ((u.erase b).prod : ℤ) := (mul_dvd_mul_iff_left hb0).mp hd
  exact hbprime.coprime_iff_not_dvd.mp hc (by exact_mod_cast hd')

theorem compensation_square_test_iff {u : List ℕ} {s N : ℤ} {p b : ℕ}
    (hu : u.Pairwise Nat.Coprime) (hb : b ∈ u) (hbprime : Nat.Prime b)
    (hbs : ¬ (b : ℤ) ∣ s) (hN : N = s * (u.prod : ℤ) * (p : ℤ)) :
    (¬ (b : ℤ) * b ∣ N) ↔ Nat.Coprime p b := by
  have hbu : (b : ℤ) ∣ (u.prod : ℤ) := by exact_mod_cast List.dvd_prod hb
  rw [prime_square_test (Nat.prime_iff_prime_int.mp hbprime) hbs hbu
    (compensation_square_not_dvd hu hb hbprime) hN]
  rw [Nat.coprime_comm,hbprime.coprime_iff_not_dvd]
  exact not_congr (by exact_mod_cast (Iff.rfl : b ∣ p ↔ b ∣ p))

theorem divisibility_iff {u : List ℕ} {s N : ℤ}
    (hu : u.Pairwise Nat.Coprime) (hs : ∀ b ∈ u, IsCoprime s (b : ℤ)) :
    s * (u.prod : ℤ) ∣ N ↔ s ∣ N ∧ ∀ b ∈ u, (b : ℤ) ∣ N := by
  change (∃ p : ℤ, N = s * (u.prod : ℤ) * p) ↔ _
  exact integrality_iff hu hs

end Ostmann.Arithmetic.HistorySupportDescent

end OAI
