import OAI.NumberTheory.Ostmann.Construction.PrimeBulkInsertion

namespace OAI

/-! # The finite primes excluded after freezing the nonbulk coordinates -/

namespace Ostmann
open scoped Classical

noncomputable def frozenPrimeDeletions {σ J : Type*} [Fintype σ]
    (base : σ → ℕ) (slot : J ↪ σ) (outside : List ℕ) : Finset ℕ :=
  Finset.univ.image (fun i : {i : σ // i ∉ Set.range slot} => base i) ∪ outside.toFinset

theorem mem_frozenPrimeDeletions_base {σ J : Type*} [Fintype σ]
    (base : σ → ℕ) (slot : J ↪ σ) (outside : List ℕ) (i : σ) (hi : i ∉ Set.range slot) :
    base i ∈ frozenPrimeDeletions base slot outside := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩

theorem mem_frozenPrimeDeletions_outside {σ J : Type*} [Fintype σ]
    (base : σ → ℕ) (slot : J ↪ σ) (outside : List ℕ) (q : ℕ) (hq : q ∈ outside) :
    q ∈ frozenPrimeDeletions base slot outside :=
  Finset.mem_union_right _ (List.mem_toFinset.mpr hq)

theorem frozenPrimeDeletions_card_le {σ J : Type*} [Fintype σ]
    (base : σ → ℕ) (slot : J ↪ σ) (outside : List ℕ) :
    (frozenPrimeDeletions base slot outside).card ≤ Fintype.card σ + outside.length := by
  have h₁ := Finset.card_image_le (s := Finset.univ)
    (f := fun i : {i : σ // i ∉ Set.range slot} => base i)
  have h₂ := Fintype.card_subtype_le (fun i : σ => i ∉ Set.range slot)
  have h₃ := List.toFinset_card_le outside
  have h₄ := Finset.card_union_le
    (Finset.univ.image (fun i : {i : σ // i ∉ Set.range slot} => base i)) outside.toFinset
  simp only [Finset.card_univ] at h₁
  exact h₄.trans (Nat.add_le_add (h₁.trans h₂) h₃)

end Ostmann

end OAI
