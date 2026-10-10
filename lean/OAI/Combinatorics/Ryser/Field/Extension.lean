import Mathlib.FieldTheory.Finite.GaloisField

namespace OAI

namespace RyserCoveringCounterexample

abbrev ExtensionField (p n : ℕ) [Fact p.Prime] := GaloisField p n

noncomputable instance extensionFieldFintype (p n : ℕ) [Fact p.Prime] :
    Fintype (ExtensionField p n) := Fintype.ofFinite _

theorem extensionField_card (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    Fintype.card (ExtensionField p n) = p ^ n := by
  simpa only [Nat.card_eq_fintype_card] using GaloisField.card p n hn

theorem extensionField_finrank (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    Module.finrank (ZMod p) (ExtensionField p n) = n :=
  GaloisField.finrank p hn

noncomputable def primeEmbedding (p n : ℕ) [Fact p.Prime] :
    ZMod p →+* ExtensionField p n := algebraMap _ _

theorem primeEmbedding_injective (p n : ℕ) [Fact p.Prime] :
    Function.Injective (primeEmbedding p n) :=
  (primeEmbedding p n).injective

@[simp] theorem primeEmbedding_eq_iff (p n : ℕ) [Fact p.Prime] (a b : ZMod p) :
    primeEmbedding p n a = primeEmbedding p n b ↔ a = b :=
  (primeEmbedding_injective p n).eq_iff

noncomputable def extensionFieldDegreeOneEquiv (p : ℕ) [Fact p.Prime] :
    ExtensionField p 1 ≃ₐ[ZMod p] ZMod p := GaloisField.equivZmodP p

end RyserCoveringCounterexample

end OAI
