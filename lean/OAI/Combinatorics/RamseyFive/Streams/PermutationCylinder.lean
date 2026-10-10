import Mathlib

namespace OAI

namespace SharpRamseyFive.PermutationCylinder
open scoped Classical
variable {α : Type*} [Fintype α]

abbrev Cylinder (S : Finset α) (e : Equiv.Perm α) :=
  {p : Equiv.Perm α // ∀ x ∈ S, p x = e x}

noncomputable instance cylinderFintype (S : Finset α) (e : Equiv.Perm α) :
    Fintype (Cylinder S e) := inferInstanceAs (Fintype {p : Equiv.Perm α // ∀ x ∈ S, p x = e x})

omit [Fintype α] in
private lemma preserves_complement (S : Finset α) (e : Equiv.Perm α)
    (p : Cylinder S e) (x : α) :
    (p.val.trans e.symm) x ∉ S ↔ x ∉ S := by
  change e.symm (p.val x) ∉ S ↔ x ∉ S
  have hf (y : α) (hy : y ∈ S) : e.symm (p.val y) = y := by rw [p.property y hy]; simp
  constructor
  · intro h hx; exact h (by rw [hf x hx]; exact hx)
  · intro h hx
    have heq : e.symm (p.val (e.symm (p.val x))) = e.symm (p.val x) := hf _ hx
    have : e.symm (p.val x) = x := p.val.injective (e.symm.injective heq)
    exact h (this ▸ hx)

noncomputable def remainingEquiv (S : Finset α) (e : Equiv.Perm α) :
    Cylinder S e ≃ Equiv.Perm {x : α // x ∉ S} where
  toFun p := Equiv.Perm.subtypePerm (p.val.trans e.symm) (preserves_complement S e p)
  invFun r := ⟨(Equiv.Perm.ofSubtype r).trans e, by
    intro x hx
    change e (Equiv.Perm.ofSubtype r x) = e x
    rw [Equiv.Perm.ofSubtype_apply_of_not_mem r (not_not.mpr hx)]⟩
  left_inv p := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change e (Equiv.Perm.ofSubtype (Equiv.Perm.subtypePerm (p.val.trans e.symm)
      (preserves_complement S e p)) x) = p.val x
    by_cases hx : x ∉ S
    · rw [Equiv.Perm.ofSubtype_apply_of_mem (p := fun z => z ∉ S) _ hx]
      change e (e.symm (p.val x)) = p.val x
      simp
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem (p := fun z => z ∉ S) _ hx]
      exact (p.property x (not_not.mp hx)).symm
  right_inv r := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change e.symm (e (Equiv.Perm.ofSubtype r x.val)) = (r x).val
    simp only [Equiv.symm_apply_apply, Equiv.Perm.ofSubtype_apply_coe]

theorem card_cylinder (S : Finset α) (e : Equiv.Perm α) :
    Fintype.card (Cylinder S e) = (Fintype.card α - S.card).factorial := by
  rw [Fintype.card_congr (remainingEquiv S e), Fintype.card_perm,
    Fintype.card_subtype_compl, Fintype.card_coe]

noncomputable def nextReference (e : Equiv.Perm α) (x y : α) : Equiv.Perm α :=
  e.trans (Equiv.swap (e x) y)

omit [Fintype α] in
lemma nextReference_at (e : Equiv.Perm α) (x y : α) : nextReference e x y x = y := by
  simp [nextReference]

omit [Fintype α] in
lemma nextReference_old (S : Finset α) (e : Equiv.Perm α) {x y : α}
    (hx : x ∉ S) (hy : y ∉ S.map e.toEmbedding) {z : α} (hz : z ∈ S) :
    nextReference e x y z = e z := by
  have hzx : e z ≠ e x := fun h => hx (e.injective h ▸ hz)
  have hzy : e z ≠ y := by
    intro h; apply hy; exact Finset.mem_map.mpr ⟨z,hz,h⟩
  simp [nextReference, Equiv.swap_apply_of_ne_of_ne hzx hzy]

noncomputable def stepEquiv (S : Finset α) (e : Equiv.Perm α) {x y : α}
    (hx : x ∉ S) (hy : y ∉ S.map e.toEmbedding) :
    {p : Cylinder S e // p.val x = y} ≃ Cylinder (insert x S) (nextReference e x y) where
  toFun p := ⟨p.val.val, by
    intro z hz
    rcases Finset.mem_insert.mp hz with h | h
    · subst z; rw [p.property, nextReference_at]
    · rw [p.val.property z h, nextReference_old S e hx hy h]⟩
  invFun p := ⟨⟨p.val, by
    intro z hz
    rw [p.property z (Finset.mem_insert_of_mem hz), nextReference_old S e hx hy hz]⟩, by
    rw [p.property x (Finset.mem_insert_self x S), nextReference_at]⟩
  left_inv p := rfl
  right_inv p := rfl

theorem card_next (S : Finset α) (e : Equiv.Perm α) {x y : α}
    (hx : x ∉ S) (hy : y ∉ S.map e.toEmbedding) :
    Fintype.card {p : Cylinder S e // p.val x = y} =
      (Fintype.card α - S.card - 1).factorial := by
  rw [Fintype.card_congr (stepEquiv S e hx hy), card_cylinder,
    Finset.card_insert_of_notMem hx, Nat.sub_add_eq]

theorem next_probability (S : Finset α) (e : Equiv.Perm α) {x y : α}
    (hx : x ∉ S) (hy : y ∉ S.map e.toEmbedding) :
    (Fintype.card {p : Cylinder S e // p.val x = y} : ℝ) /
      Fintype.card (Cylinder S e) = 1 / (Fintype.card α - S.card : ℕ) := by
  have hs : S.card < Fintype.card α := by
    have hs' := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨S.subset_univ, fun he => hx (he ▸ Finset.mem_univ x)⟩)
    simpa using hs'
  have hn : 0 < Fintype.card α - S.card := Nat.sub_pos_of_lt hs
  have he : Fintype.card α - S.card = (Fintype.card α - S.card - 1) + 1 := by omega
  rw [card_next S e hx hy, card_cylinder]
  conv_rhs => rw [he]
  rw [he, Nat.factorial_succ]
  have hf : ((Fintype.card α - S.card - 1).factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

end SharpRamseyFive.PermutationCylinder

end OAI
