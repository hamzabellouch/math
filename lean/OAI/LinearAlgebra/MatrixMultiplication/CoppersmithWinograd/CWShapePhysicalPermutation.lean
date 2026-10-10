import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWStrands
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.TensorSidePermutation

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

namespace MatrixMultiplication.CWShapePhysicalPermutation

open MatrixMultiplication.Foundation CWStrands
open scoped BigOperators

variable {F : Type*} [CommRing F]

private theorem tensor_swapXY (q : ℕ) (x y z : Fin (q + 2)) :
    FieldCW.tensor F q x y z = FieldCW.tensor F q y x z := by
  unfold FieldCW.tensor
  simp only [Finset.sum_add_distrib, mul_comm, mul_left_comm, mul_assoc]
  ring

private theorem tensor_swapYZ (q : ℕ) (x y z : Fin (q + 2)) :
    FieldCW.tensor F q x y z = FieldCW.tensor F q x z y := by
  exact (FieldCW.tensor_cyclic F q x y z).trans
    ((tensor_swapXY q y z x).trans (FieldCW.tensor_cyclic F q x z y).symm)

private theorem tensor_swapXZ (q : ℕ) (x y z : Fin (q + 2)) :
    FieldCW.tensor F q x y z = FieldCW.tensor F q z y x := by
  exact (FieldCW.tensor_cyclic F q x y z).trans (tensor_swapXY q y z x)

theorem tensor_permute (q : ℕ) (σ : Equiv.Perm (Fin 3))
    (a : Fin 3 → Fin (q + 2)) :
    FieldCW.tensor F q (a (σ 0)) (a (σ 1)) (a (σ 2)) =
      FieldCW.tensor F q (a 0) (a 1) (a 2) := by
  have h01 : σ 0 ≠ σ 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (σ.injective h)
  have h02 : σ 0 ≠ σ 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (σ.injective h)
  have h12 : σ 1 ≠ σ 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (σ.injective h)
  generalize hs0 : σ 0 = s0 at *
  generalize hs1 : σ 1 = s1 at *
  generalize hs2 : σ 2 = s2 at *
  fin_cases s0 <;> fin_cases s1 <;> fin_cases s2 <;> try contradiction
  · rfl
  · exact (tensor_swapYZ q (a 0) (a 1) (a 2)).symm
  · exact (tensor_swapXY q (a 0) (a 1) (a 2)).symm
  · exact (FieldCW.tensor_cyclic F q (a 0) (a 1) (a 2)).symm
  · exact FieldCW.tensor_cyclic F q (a 2) (a 0) (a 1)
  · exact (tensor_swapXZ q (a 0) (a 1) (a 2)).symm

theorem strand_permute {P : Type*} [Fintype P]
    (σ : Equiv.Perm (Fin 3)) (a : Fin 3 → P → Fin 7) :
    strand (F := F) P (a (σ 0)) (a (σ 1)) (a (σ 2)) =
      strand P (a 0) (a 1) (a 2) := by
  apply Finset.prod_congr rfl
  intro i _
  exact tensor_permute 5 σ (fun s => a s i)

theorem shapeTensor_permute {P : Type*} [Fintype P]
    (σ : Equiv.Perm (Fin 3)) (g : Fin 3 → ℕ) (a : Fin 3 → P → Fin 7) :
    shapeTensor (F := F) P (g ∘ σ) (a (σ 0)) (a (σ 1)) (a (σ 2)) =
      shapeTensor P g (a 0) (a 1) (a 2) := by
  have hmask :
      (weight (a (σ 0)) = g (σ 0) ∧ weight (a (σ 1)) = g (σ 1) ∧
        weight (a (σ 2)) = g (σ 2)) ↔
      (weight (a 0) = g 0 ∧ weight (a 1) = g 1 ∧ weight (a 2) = g 2) := by
    constructor
    · rintro ⟨h0, h1, h2⟩
      have hs (s : Fin 3) : weight (a (σ s)) = g (σ s) := by
        fin_cases s <;> assumption
      exact ⟨by simpa using hs (σ.symm 0), by simpa using hs (σ.symm 1),
        by simpa using hs (σ.symm 2)⟩
    · rintro ⟨h0, h1, h2⟩
      have hs (s : Fin 3) : weight (a s) = g s := by
        fin_cases s <;> assumption
      exact ⟨hs (σ 0), hs (σ 1), hs (σ 2)⟩
  have hp := strand_permute (F := F) σ a
  simp only [shapeTensor, Function.comp_apply, hmask, hp]

theorem shapeTensor_prod_permute {I : Type*} [Fintype I]
    (P : I → Type*) [∀ i, Fintype (P i)]
    (σ : I → Equiv.Perm (Fin 3)) (g : I → Fin 3 → ℕ)
    (a : ∀ i, Fin 3 → P i → Fin 7) :
    (∏ i, shapeTensor (F := F) (P i) (g i ∘ σ i)
      (a i (σ i 0)) (a i (σ i 1)) (a i (σ i 2))) =
      ∏ i, shapeTensor (P i) (g i) (a i 0) (a i 1) (a i 2) := by
  apply Finset.prod_congr rfl
  intro i _
  exact shapeTensor_permute (σ i) (g i) (a i)

theorem shapeTensor_prod_permute_ne_zero_iff {I : Type*} [Fintype I]
    (P : I → Type*) [∀ i, Fintype (P i)]
    (σ : I → Equiv.Perm (Fin 3)) (g : I → Fin 3 → ℕ)
    (a : ∀ i, Fin 3 → P i → Fin 7) :
    (∏ i, shapeTensor (F := F) (P i) (g i ∘ σ i)
      (a i (σ i 0)) (a i (σ i 1)) (a i (σ i 2))) ≠ 0 ↔
      (∏ i, shapeTensor (F := F) (P i) (g i) (a i 0) (a i 1) (a i 2)) ≠ 0 := by
  rw [shapeTensor_prod_permute]

theorem sidePermutation_shapeTensor {P : Type*} [Fintype P]
    (σ : Equiv.Perm (Fin 3)) (g : Fin 3 → ℕ) :
    Tensor.sidePermutation σ (shapeTensor (F := F) P g) =
      shapeTensor P (g ∘ σ) := by
  funext x y z
  let a : Fin 3 → P → Fin 7 := ![x, y, z]
  change Tensor.sidePermutation σ (shapeTensor P g) (a 0) (a 1) (a 2) =
    shapeTensor P (g ∘ σ) (a 0) (a 1) (a 2)
  rw [Tensor.sidePermutation_apply_coordinates]
  have h := shapeTensor_permute (F := F) σ g (fun s => a (σ.symm s))
  simpa only [Equiv.symm_apply_apply] using h.symm

end MatrixMultiplication.CWShapePhysicalPermutation

end

end OAI
