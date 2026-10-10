import OAI.Combinatorics.Ryser.Field.ExtensionSubfields
import Mathlib.Algebra.Ring.Parity
import Lean.Elab.Tactic.Omega

namespace OAI

/-!
Proper subfields in every odd extension degree. The degree divisor and its
properness are derived from actual finite-field cardinalities, not assumed of
the splitting field chosen by the construction.
-/
namespace RyserCoveringCounterexample

/-- A proper divisor of a positive odd number has index at least three. -/
theorem three_mul_le_of_dvd_odd {d n : ℕ} (hn : Odd n) (hd : d ∣ n)
    (hne : d ≠ n) : 3 * d ≤ n := by
  obtain ⟨a, ha⟩ := hn
  obtain ⟨q, hq⟩ := hd
  have hq3 : 3 ≤ q := by
    by_contra h
    have hc : q = 0 ∨ q = 1 ∨ q = 2 := by omega
    rcases hc with h0 | h1 | h2
    · subst q
      simp only [Nat.mul_zero] at hq
      omega
    · subst q
      simp only [Nat.mul_one] at hq
      omega
    · subst q
      simp only [Nat.mul_two] at hq
      omega
  calc
    3 * d = d * 3 := Nat.mul_comm _ _
    _ ≤ d * q := Nat.mul_le_mul_left d hq3
    _ = n := hq.symm

variable {F : Type*} [Field F] [Fintype F]
variable {p n : ℕ} [CharP F p]

/-- The actual degree of a proper subfield divides the odd ambient degree and
is at most one third of it. No primality assumption on the degree is used. -/
theorem subfield_degree_data_of_odd (hp : p.Prime) (hn : Odd n)
    (hcard : Fintype.card F = p ^ n) (S : Subfield F) [Fintype S]
    (hS : S ≠ ⊤) :
    ∃ d : ℕ, 0 < d ∧ d ∣ n ∧ 3 * d ≤ n ∧ Fintype.card S = p ^ d := by
  obtain ⟨m, _, hm⟩ := FiniteField.card S p
  have hpow : p ^ n = p ^ ((m : ℕ) * Module.finrank S F) := by
    calc
      p ^ n = Fintype.card F := hcard.symm
      _ = Fintype.card S ^ Module.finrank S F :=
        Module.card_eq_pow_finrank (K := S) (V := F)
      _ = (p ^ (m : ℕ)) ^ Module.finrank S F := by rw [hm]
      _ = p ^ ((m : ℕ) * Module.finrank S F) :=
        (pow_mul p (m : ℕ) (Module.finrank S F)).symm
  have hdegree : n = (m : ℕ) * Module.finrank S F :=
    Nat.pow_right_injective hp.one_lt hpow
  have hdiv : (m : ℕ) ∣ n := ⟨Module.finrank S F, hdegree⟩
  have hne : (m : ℕ) ≠ n := by
    intro he
    have hlt := subfield_card_lt_of_ne_top S hS
    have hsame : Fintype.card S = Fintype.card F := by rw [hm, he, hcard]
    exact (ne_of_lt hlt) hsame
  exact ⟨m, m.property, hdiv, three_mul_le_of_dvd_odd hn hdiv hne, hm⟩

/-- Cube bound for proper subfields in arbitrary odd degree, including composite degree. -/
theorem subfield_card_cube_le_of_odd_degree (hp : p.Prime) (hn : Odd n)
    (hcard : Fintype.card F = p ^ n) (S : Subfield F) [Fintype S]
    (hS : S ≠ ⊤) : Fintype.card S ^ 3 ≤ Fintype.card F := by
  obtain ⟨d, _, _, hd, hSd⟩ := subfield_degree_data_of_odd hp hn hcard S hS
  rw [hSd, hcard, ← pow_mul]
  exact Nat.pow_le_pow_right hp.pos (by simpa only [Nat.mul_comm] using hd)

/-- Choice-free cardinal version of the arbitrary odd-degree cube bound. -/
theorem subfield_natCard_cube_le_of_odd_degree (hp : p.Prime) (hn : Odd n)
    (hcard : Fintype.card F = p ^ n) (S : Subfield F) (hS : S ≠ ⊤) :
    Nat.card S ^ 3 ≤ Fintype.card F := by
  classical
  let : Fintype S := Fintype.ofFinite S
  simpa only [Nat.card_eq_fintype_card] using
    subfield_card_cube_le_of_odd_degree hp hn hcard S hS

/-- The constructed splitting field satisfies the required cube bound for every
odd degree above two, with no hypothesis on its proper subfields. -/
theorem extensionField_properSubfield_cube_le_of_odd (p n : ℕ) [Fact p.Prime]
    (hn : Odd n) (_hn3 : 2 < n) (S : Subfield (ExtensionField p n)) (hS : S ≠ ⊤) :
    Nat.card S ^ 3 ≤ Fintype.card (ExtensionField p n) := by
  have hn0 : n ≠ 0 := by obtain ⟨a, ha⟩ := hn; omega
  exact subfield_natCard_cube_le_of_odd_degree (Fact.out : p.Prime) hn
    (extensionField_card p n hn0) S hS

/-- Same bound with the actual ambient cardinality written as its prime power. -/
theorem extensionField_properSubfield_cube_le_pow_of_odd (p n : ℕ) [Fact p.Prime]
    (hn : Odd n) (hn3 : 2 < n) (S : Subfield (ExtensionField p n)) (hS : S ≠ ⊤) :
    Nat.card S ^ 3 ≤ p ^ n := by
  have hn0 : n ≠ 0 := by omega
  rw [← extensionField_card p n hn0]
  exact extensionField_properSubfield_cube_le_of_odd p n hn hn3 S hS

end RyserCoveringCounterexample

end OAI
