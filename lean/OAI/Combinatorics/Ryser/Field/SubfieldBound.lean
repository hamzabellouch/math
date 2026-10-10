import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.FieldTheory.Finite.Basic

namespace OAI

namespace RyserCoveringCounterexample

variable {F : Type*} [Field F] [Fintype F]

theorem subfield_card_lt_of_ne_top (S : Subfield F) [Fintype S]
    (hS : S ≠ ⊤) : Fintype.card S < Fintype.card F := by
  apply Fintype.card_lt_of_injective_not_surjective
    (fun x : S => (x : F)) Subtype.val_injective
  intro hsurj
  apply hS
  apply top_unique
  intro x _
  obtain ⟨y, hy⟩ := hsurj x
  exact hy ▸ y.property

theorem subfield_natCard_lt_of_ne_top (S : Subfield F)
    (hS : S ≠ ⊤) : Nat.card S < Fintype.card F := by
  classical
  let : Fintype S := Fintype.ofFinite S
  simpa only [Nat.card_eq_fintype_card] using subfield_card_lt_of_ne_top S hS

variable {p n : ℕ} [CharP F p]

theorem subfield_card_eq_char_of_prime_degree (hp : p.Prime) (hn : n.Prime)
    (hcard : Fintype.card F = p ^ n) (S : Subfield F) [Fintype S]
    (hS : S ≠ ⊤) : Fintype.card S = p := by
  obtain ⟨m, _, hm⟩ := FiniteField.card S p
  have hpow : p ^ n = p ^ ((m : ℕ) * Module.finrank S F) := by
    calc
      p ^ n = Fintype.card F := hcard.symm
      _ = Fintype.card S ^ Module.finrank S F :=
        Module.card_eq_pow_finrank (K := S) (V := F)
      _ = (p ^ (m : ℕ)) ^ Module.finrank S F := by rw [hm]
      _ = p ^ ((m : ℕ) * Module.finrank S F) :=
        (pow_mul p (m : ℕ) (Module.finrank S F)).symm
  have hnmd : n = (m : ℕ) * Module.finrank S F :=
    Nat.pow_right_injective hp.one_lt hpow
  have hmdiv : (m : ℕ) ∣ n := ⟨Module.finrank S F, hnmd⟩
  rcases hn.eq_one_or_self_of_dvd (m : ℕ) hmdiv with hmone | hmn
  · simpa only [hmone, pow_one] using hm
  · have hlt := subfield_card_lt_of_ne_top S hS
    have heq : Fintype.card S = Fintype.card F := by rw [hm, hmn, hcard]
    exact ((ne_of_lt hlt) heq).elim

theorem subfield_natCard_eq_char_of_prime_degree (hp : p.Prime) (hn : n.Prime)
    (hcard : Fintype.card F = p ^ n) (S : Subfield F)
    (hS : S ≠ ⊤) : Nat.card S = p := by
  classical
  let : Fintype S := Fintype.ofFinite S
  simpa only [Nat.card_eq_fintype_card] using
    subfield_card_eq_char_of_prime_degree hp hn hcard S hS

theorem subfield_card_cube_le_of_prime_degree (hp : p.Prime) (hn : n.Prime)
    (hcard : Fintype.card F = p ^ n) (hn3 : 2 < n)
    (S : Subfield F) [Fintype S] (hS : S ≠ ⊤) :
    Fintype.card S ^ 3 ≤ Fintype.card F := by
  rw [subfield_card_eq_char_of_prime_degree hp hn hcard S hS, hcard]
  exact Nat.pow_le_pow_right hp.pos (Nat.succ_le_of_lt hn3)

theorem subfield_natCard_cube_le_of_prime_degree (hp : p.Prime) (hn : n.Prime)
    (hcard : Fintype.card F = p ^ n) (hn3 : 2 < n)
    (S : Subfield F) (hS : S ≠ ⊤) : Nat.card S ^ 3 ≤ Fintype.card F := by
  rw [subfield_natCard_eq_char_of_prime_degree hp hn hcard S hS, hcard]
  exact Nat.pow_le_pow_right hp.pos (Nat.succ_le_of_lt hn3)

theorem subfield_eq_top_of_card_eq_char (hp : p.Prime)
    (hcard : Fintype.card F = p) (S : Subfield F) : S = ⊤ := by
  classical
  let : Fintype S := Fintype.ofFinite S
  by_contra hS
  obtain ⟨m, _, hm⟩ := FiniteField.card S p
  have hpS : p ≤ Fintype.card S := by
    rw [hm]
    simpa only [pow_one] using
      (Nat.pow_le_pow_right hp.pos m.property : p ^ 1 ≤ p ^ (m : ℕ))
  have hlt := subfield_card_lt_of_ne_top S hS
  rw [hcard] at hlt
  exact (not_lt_of_ge hpS) hlt

end RyserCoveringCounterexample

end OAI
