import OAI.NumberTheory.Ostmann.Arithmetic.MovingCoefficientSupport

namespace OAI

/-! # The restored child lists supply the support used by the transfer -/

namespace Ostmann
open scoped Classical BigOperators

/-- Restoring compensation does not change its order-free current support. -/
theorem movingFrequencyCoefficient_child_pairwise {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ)
    (u small bulk : TreeLeafTuple (List σ) n) (p X : ℕ)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n s
      (appendMovingSlotLeaves n u small) bulk p X ≠ 0) :
    (p :: X :: ((flattenMovingSlots n u).map value ++
      ((flattenMovingSlots n small ++ flattenMovingSlots n bulk).map value ++ outside))).Pairwise Nat.Coprime := by
  have hs := (movingFrequencyCoefficient_nonzero_support value outside μ childBound
    pivotBound V F φ G n s (appendMovingSlotLeaves n u small) bulk p X h).1
  have hp := (flattenMovingSlots_append_perm n u small).append_right (flattenMovingSlots n bulk)
  have hp' := (((hp.map value).append_right outside).cons X).cons p
  apply (hp'.pairwise_iff (fun h => h.symm)).mp at hs
  simpa only [List.map_append, List.append_assoc] using hs

/-- A restored child is disjoint from the inserted giant and its shared
compensation vector. These are precisely the product units needed in the
integer substitution. -/
theorem restored_child_product_support (u small outside : List ℕ) (p X : ℕ)
    (h : (p :: X :: (u ++ (small ++ outside))).Pairwise Nat.Coprime) :
    (X :: (small ++ outside)).Pairwise Nat.Coprime ∧
      (X * small.prod).Coprime (p * u.prod) := by
  obtain ⟨hp, htail⟩ := List.pairwise_cons.mp h
  obtain ⟨hX, hrest⟩ := List.pairwise_cons.mp htail
  obtain ⟨_, hsmall, hcross⟩ := List.pairwise_append.mp hrest
  refine ⟨List.pairwise_cons.mpr ⟨?_, hsmall⟩, ?_⟩
  · exact fun a ha => hX a (List.mem_append_right u ha)
  · apply Nat.Coprime.mul_right
    · apply Nat.Coprime.mul_left
      · exact (hp X List.mem_cons_self).symm
      · apply Nat.coprime_list_prod_left_iff.mpr
        intro a ha
        exact (hp a (List.mem_cons_of_mem X
          (List.mem_append_right u (List.mem_append_left outside ha)))).symm
    · apply Nat.coprime_list_prod_right_iff.mpr
      intro a ha
      apply Nat.Coprime.mul_left
      · exact hX a (List.mem_append_left (small ++ outside) ha)
      · apply Nat.coprime_list_prod_left_iff.mpr
        intro b hb
        exact (hcross a ha b (List.mem_append_left outside hb)).symm

/-- The inherited product in a nonzero child is coprime to the composite
pivot, even when the newly inserted giant is only an integer. -/
theorem movingFrequencyCoefficient_child_products {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ)
    (u small bulk : TreeLeafTuple (List σ) n) (p X : ℕ)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G n s
      (appendMovingSlotLeaves n u small) bulk p X ≠ 0) :
    (X :: (((flattenMovingSlots n small ++ flattenMovingSlots n bulk).map value) ++ outside)).Pairwise Nat.Coprime ∧
      (X * MovingSlotReversal.naturalProduct value
        (flattenMovingSlots n small ++ flattenMovingSlots n bulk)).Coprime
        (p * MovingSlotReversal.naturalProduct value (flattenMovingSlots n u)) := by
  exact restored_child_product_support _ _ _ p X
    (movingFrequencyCoefficient_child_pairwise value outside μ childBound pivotBound V F φ G
      n s u small bulk p X h)

end Ostmann

end OAI
