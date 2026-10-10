import OAI.NumberTheory.Ostmann.Preliminaries.FullSummandResidues

namespace OAI

/-! # The exact forbidden classes of finitely many distinct shifts -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def finiteShiftAllowed (B : Finset ℕ) (p : ℕ) : Finset (ZMod p) :=
  ((Finset.range p).image fun r : ℕ => (r : ZMod p)) \
    (B.image fun b : ℕ => -(b : ZMod p))

 theorem zmod_range_image (p : ℕ) [NeZero p] :
    ((Finset.range p).image fun r : ℕ => (r : ZMod p)) = Finset.univ := by
  ext x
  constructor
  · intro _
    exact Finset.mem_univ x
  · intro _
    exact Finset.mem_image.mpr ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩

 theorem finiteShiftAllowed_card (B : Finset ℕ) (p : ℕ) [NeZero p]
    (hB : ∀ b ∈ B, b < p) : (finiteShiftAllowed B p).card + B.card = p := by
  have hinj : Set.InjOn (fun b : ℕ => -(b : ZMod p)) B := by
    intro a ha b hb he
    have hmod := (ZMod.natCast_eq_natCast_iff' a b p).mp (neg_injective he)
    simpa only [Nat.mod_eq_of_lt (hB a ha), Nat.mod_eq_of_lt (hB b hb)] using hmod
  rw [finiteShiftAllowed, zmod_range_image, ← Finset.card_image_of_injOn hinj,
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ, ZMod.card]

 theorem finiteShiftAllowed_mem_of_prime (B : Finset ℕ) (p a : ℕ) [NeZero p]
    (hp : p.Prime) (ha : p < a) (hprime : ∀ b ∈ B, (a + b).Prime) :
    (a : ZMod p) ∈ finiteShiftAllowed B p := by
  rw [finiteShiftAllowed, zmod_range_image]
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hmem
  obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hmem
  have hdvd : p ∣ a + b := by
    apply (ZMod.natCast_eq_zero_iff (a + b) p).mp
    rw [Nat.cast_add, ← he]
    simp
  have heq := ((hprime b hb).dvd_iff_eq hp.one_lt.ne').mp hdvd
  omega

end Ostmann

end OAI
