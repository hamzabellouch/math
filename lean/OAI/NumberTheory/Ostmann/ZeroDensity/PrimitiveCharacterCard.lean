import OAI.NumberTheory.Ostmann.ZeroDensity.PublishedComplexZeroDensity

namespace OAI

/-! # The elementary conductor-family cardinality bound -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def PrimitiveComplexCharacter.atModulus (χ : PrimitiveComplexCharacter)
    (q : ℕ) (h : χ.modulus = q) : DirichletCharacter ℂ q := h ▸ χ.character

theorem primitive_character_fiber_card (F : Finset PrimitiveComplexCharacter)
    (q : ℕ) (hq : 0 < q) : (F.filter (fun χ => χ.modulus = q)).card ≤ q := by
  let S := F.filter (fun χ => χ.modulus = q)
  let f : S → DirichletCharacter ℂ q := fun χ =>
    χ.val.atModulus q (Finset.mem_filter.mp χ.property).2
  have hf : Function.Injective f := by
    intro χ ψ he
    apply Subtype.ext
    have hχ := (Finset.mem_filter.mp χ.property).2
    have hψ := (Finset.mem_filter.mp ψ.property).2
    obtain ⟨⟨m, hm, c, hc, hn⟩, hmem⟩ := χ
    obtain ⟨⟨n, hp, d, hd, hd'⟩, hmem'⟩ := ψ
    dsimp at hχ hψ
    subst m
    subst n
    dsimp [f, PrimitiveComplexCharacter.atModulus] at he
    cases he
    rfl
  have : NeZero q := ⟨hq.ne'⟩
  calc
    _ = Fintype.card S := (Fintype.card_coe S).symm
    _ ≤ Fintype.card (DirichletCharacter ℂ q) := Fintype.card_le_of_injective f hf
    _ = q.totient := by
      rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    _ ≤ q := Nat.totient_le q

theorem primitive_character_family_card (F : Finset PrimitiveComplexCharacter)
    (Q : ℕ) (hF : ∀ χ ∈ F, χ.modulus ≤ Q) : F.card ≤ Q ^ 2 := by
  have hmap : (F : Set PrimitiveComplexCharacter).MapsTo
      PrimitiveComplexCharacter.modulus (Finset.Icc 1 Q) := by
    intro χ hχ
    exact Finset.mem_Icc.mpr ⟨χ.positive, hF χ hχ⟩
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, Q := by
      apply Finset.sum_le_sum
      intro q hq
      exact (primitive_character_fiber_card F q (Finset.mem_Icc.mp hq).1).trans
        (Finset.mem_Icc.mp hq).2
    _ = Q ^ 2 := by simp [Nat.card_Icc, pow_two]

end Ostmann

end OAI
