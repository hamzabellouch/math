import OAI.Combinatorics.Ryser.Field.Extension
import OAI.Combinatorics.Ryser.Field.SubfieldBound

namespace OAI

namespace RyserCoveringCounterexample

theorem extensionField_properSubfield_card (p n : ℕ) [Fact p.Prime]
    (hn : n.Prime) (S : Subfield (ExtensionField p n)) (hS : S ≠ ⊤) :
    Nat.card S = p :=
  subfield_natCard_eq_char_of_prime_degree (Fact.out : p.Prime) hn
    (extensionField_card p n hn.ne_zero) S hS

theorem extensionField_properSubfield_cube_le (p n : ℕ) [Fact p.Prime]
    (hn : n.Prime) (hn3 : 2 < n) (S : Subfield (ExtensionField p n)) (hS : S ≠ ⊤) :
    Nat.card S ^ 3 ≤ Fintype.card (ExtensionField p n) :=
  subfield_natCard_cube_le_of_prime_degree (Fact.out : p.Prime) hn
    (extensionField_card p n hn.ne_zero) hn3 S hS

theorem extensionField_properSubfield_cube_le_pow (p n : ℕ) [Fact p.Prime]
    (hn : n.Prime) (hn3 : 2 < n) (S : Subfield (ExtensionField p n)) (hS : S ≠ ⊤) :
    Nat.card S ^ 3 ≤ p ^ n := by
  rw [← extensionField_card p n hn.ne_zero]
  exact extensionField_properSubfield_cube_le p n hn hn3 S hS

theorem primeField_subfield_eq_top (p : ℕ) [Fact p.Prime]
    (S : Subfield (ZMod p)) : S = ⊤ :=
  subfield_eq_top_of_card_eq_char (Fact.out : p.Prime) (ZMod.card p) S

theorem extensionField_degree_one_subfield_eq_top (p : ℕ) [Fact p.Prime]
    (S : Subfield (ExtensionField p 1)) : S = ⊤ := by
  apply subfield_eq_top_of_card_eq_char (Fact.out : p.Prime) (S := S)
  simpa only [pow_one] using extensionField_card p 1 one_ne_zero

end RyserCoveringCounterexample

end OAI
