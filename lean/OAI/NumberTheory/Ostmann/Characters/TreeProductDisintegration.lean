import OAI.NumberTheory.Ostmann.Characters.TreeSplitCoordinates

namespace OAI

/-! # Disintegrating the original independent leaf law by its total product -/

namespace Ostmann

open scoped BigOperators

theorem sum_treeLeafTuple_dependent {G : Type} [CommGroup G] [Fintype G]
    (n : ℕ) (F : (P : G) → TreeLeafFiber G n P → ℝ) :
    (∑ x : TreeLeafTuple G n, F (treeLeafProduct n x) ⟨x, rfl⟩) =
      ∑ P : G, ∑ x : TreeLeafFiber G n P, F P x := by
  rw [sum_treeLeafTuple_by_product]
  apply Finset.sum_congr rfl
  intro P _
  apply Finset.sum_congr rfl
  rintro ⟨x, hx⟩ _
  cases hx
  rfl

theorem treeLeaf_average_by_product {G : Type} [CommGroup G] [Fintype G]
    (n : ℕ) (F : (P : G) → TreeLeafFiber G n P → ℝ) :
    (Fintype.card (TreeLeafTuple G n) : ℝ)⁻¹ *
        (∑ x : TreeLeafTuple G n, F (treeLeafProduct n x) ⟨x, rfl⟩) =
      (Fintype.card G : ℝ)⁻¹ * ∑ P : G,
        (Fintype.card (TreeLeafFiber G n P) : ℝ)⁻¹ * ∑ x, F P x := by
  rw [sum_treeLeafTuple_dependent]
  simp only [card_treeLeafTuple, card_treeLeafFiber, Nat.cast_pow]
  rw [← Finset.mul_sum, ← mul_assoc, ← mul_inv, ← pow_succ']
  have hcount : 2 ^ n - 1 + 1 = 2 ^ n := Nat.sub_add_cancel Nat.one_le_two_pow
  rw [hcount]

/-- A bound uniform in the exposed product is also a bound for the
original independent leaf samples. -/
theorem treeLeaf_average_le {G : Type} [CommGroup G] [Fintype G]
    (n : ℕ) (F : (P : G) → TreeLeafFiber G n P → ℝ) (B : ℝ)
    (hF : ∀ P, (Fintype.card (TreeLeafFiber G n P) : ℝ)⁻¹ * ∑ x, F P x ≤ B) :
    (Fintype.card (TreeLeafTuple G n) : ℝ)⁻¹ *
        (∑ x : TreeLeafTuple G n, F (treeLeafProduct n x) ⟨x, rfl⟩) ≤ B := by
  rw [treeLeaf_average_by_product]
  calc
    _ ≤ (Fintype.card G : ℝ)⁻¹ * ∑ _P : G, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun P _ => hF P) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

end Ostmann

end OAI
