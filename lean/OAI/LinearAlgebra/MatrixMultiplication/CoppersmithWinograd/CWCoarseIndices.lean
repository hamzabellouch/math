import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWStrands

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

namespace MatrixMultiplication.CWCoarseIndices

open MatrixMultiplication.Foundation CWStrands
open scoped BigOperators

theorem label_weight_le_two : ∀ x : Fin 7, CWLeafStatistics.weight x ≤ 2 := by
  decide +kernel

theorem weight_le {P : Type*} [Fintype P] (w : P → Fin 7) :
    weight w ≤ 2 * Fintype.card P := by
  calc
    weight w ≤ ∑ _i : P, 2 := Finset.sum_le_sum fun i _ => label_weight_le_two (w i)
    _ = _ := by simp [Nat.mul_comm]

def coarseIndex {P : Type*} [Fintype P] (hP : Fintype.card P ≤ 8)
    (w : P → Fin 7) : Fin 17 := ⟨weight w, by have := weight_le w; omega⟩

theorem strand_coarse_support {F P : Type*} [CommRing F] [Fintype P]
    (hP : Fintype.card P ≤ 8) (x y z : P → Fin 7)
    (h : strand (F := F) P x y z ≠ 0) :
    (coarseIndex hP x).val + (coarseIndex hP y).val + (coarseIndex hP z).val =
      2 * Fintype.card P := strand_support x y z h

theorem split_coarse_support {F P Q : Type*} [CommRing F] [Fintype P] [Fintype Q]
    (hP : Fintype.card P ≤ 8) (g : Fin 3 → ℕ)
    (x : (P → Fin 7) × (Q → Fin 7))
    (y : (P → Fin 7) × (Q → Fin 7))
    (z : (P → Fin 7) × (Q → Fin 7))
    (h : shapeTensor (F := F) (P ⊕ Q) g (Sum.elim x.1 x.2)
      (Sum.elim y.1 y.2) (Sum.elim z.1 z.2) ≠ 0) :
    ((coarseIndex hP x.1).val + (coarseIndex hP y.1).val +
        (coarseIndex hP z.1).val = 2 * Fintype.card P) ∧
      (coarseIndex hP x.1).val ≤ g 0 ∧ (coarseIndex hP y.1).val ≤ g 1 ∧
        (coarseIndex hP z.1).val ≤ g 2 := by
  have hshape := shapeTensor_support g _ _ _ h
  have ht : strand (F := F) (P ⊕ Q) (Sum.elim x.1 x.2)
      (Sum.elim y.1 y.2) (Sum.elim z.1 z.2) ≠ 0 := by
    simpa only [shapeTensor, ite_eq_left hshape] using h
  rw [strand_sum_elim, Tensor.product] at ht
  have hl : strand (F := F) P x.1 y.1 z.1 ≠ 0 := by
    intro he
    exact ht (by rw [he, zero_mul])
  refine ⟨strand_coarse_support hP x.1 y.1 z.1 hl, ?_, ?_, ?_⟩
  · have hs := hshape.1
    rw [weight_sum_elim] at hs
    exact hs ▸ Nat.le_add_right (weight x.1) (weight x.2)
  · have hs := hshape.2.1
    rw [weight_sum_elim] at hs
    exact hs ▸ Nat.le_add_right (weight y.1) (weight y.2)
  · have hs := hshape.2.2
    rw [weight_sum_elim] at hs
    exact hs ▸ Nat.le_add_right (weight z.1) (weight z.2)

end MatrixMultiplication.CWCoarseIndices

end

end OAI
