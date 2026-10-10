import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.InitialState

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

open scoped BigOperators

namespace MatrixMultiplication.Foundation.Tensor

variable {K X Y : Type*}

def sidePermutation (σ : Equiv.Perm (Fin 3)) (T : Tensor K X X X) :
    Tensor K X X X :=
  fun x y z => T ((Matrix.vecCons (x) (Matrix.vecCons (y) (Matrix.vecCons (z) Matrix.vecEmpty))) (σ.symm 0))
    ((Matrix.vecCons (x) (Matrix.vecCons (y) (Matrix.vecCons (z) Matrix.vecEmpty))) (σ.symm 1)) ((Matrix.vecCons (x) (Matrix.vecCons (y) (Matrix.vecCons (z) Matrix.vecEmpty))) (σ.symm 2))

private theorem coordinates_eta (a : Fin 3 → X) : (Matrix.vecCons (a 0) (Matrix.vecCons (a 1) (Matrix.vecCons (a 2) Matrix.vecEmpty))) = a := by
  funext i
  fin_cases i <;> rfl

theorem sidePermutation_apply_coordinates (σ : Equiv.Perm (Fin 3))
    (T : Tensor K X X X) (a : Fin 3 → X) :
    sidePermutation σ T (a 0) (a 1) (a 2) =
      T (a (σ.symm 0)) (a (σ.symm 1)) (a (σ.symm 2)) := by
  simp only [sidePermutation, coordinates_eta]

@[simp] theorem sidePermutation_refl (T : Tensor K X X X) :
    sidePermutation (Equiv.refl _) T = T := by
  rfl

@[simp] theorem sidePermutation_symm (σ : Equiv.Perm (Fin 3))
    (T : Tensor K X X X) :
    sidePermutation σ.symm (sidePermutation σ T) = T := by
  funext x y z
  let a : Fin 3 → X := (Matrix.vecCons (x) (Matrix.vecCons (y) (Matrix.vecCons (z) Matrix.vecEmpty)))
  change sidePermutation σ.symm (sidePermutation σ T) (a 0) (a 1) (a 2) = T x y z
  rw [sidePermutation_apply_coordinates]
  change sidePermutation σ T ((fun i => a (σ i)) 0)
    ((fun i => a (σ i)) 1) ((fun i => a (σ i)) 2) = T x y z
  rw [sidePermutation_apply_coordinates σ T (fun i => a (σ i))]
  simp [a]

@[simp] theorem sidePermutation_apply_symm (σ : Equiv.Perm (Fin 3))
    (T : Tensor K X X X) :
    sidePermutation σ (sidePermutation σ.symm T) = T :=
  sidePermutation_symm σ.symm T

private def coordinatesEquiv (X : Type*) : (X × X × X) ≃ (Fin 3 → X) where
  toFun a := (Matrix.vecCons (a.1) (Matrix.vecCons (a.2.1) (Matrix.vecCons (a.2.2) Matrix.vecEmpty)))
  invFun a := (a 0, a 1, a 2)
  left_inv _ := rfl
  right_inv := coordinates_eta

private def permuteCoordinates (σ : Equiv.Perm (Fin 3)) (X : Type*) :
    (Fin 3 → X) ≃ (Fin 3 → X) where
  toFun a := fun i => a (σ.symm i)
  invFun a := fun i => a (σ i)
  left_inv a := by funext i; simp
  right_inv a := by funext i; simp

variable [CommSemiring K] [Fintype X]

private theorem restrict_eq_sum_coordinates (M : Fin 3 → Y → X → K)
    (T : Tensor K X X X) (a : Fin 3 → Y) :
    restrict (M 0) (M 1) (M 2) T (a 0) (a 1) (a 2) =
      ∑ b : Fin 3 → X, (∏ i, M i (a i) (b i)) * T (b 0) (b 1) (b 2) := by
  classical
  rw [← (coordinatesEquiv X).sum_comp
    (fun coordinates => (∏ index, M index (a index) (coordinates index)) *
      T (coordinates 0) (coordinates 1) (coordinates 2))]
  simp only [Fintype.sum_prod_type, Fin.prod_univ_three]
  rfl

theorem restrict_sidePermutation (σ : Equiv.Perm (Fin 3))
    (M : Fin 3 → Y → X → K) (T : Tensor K X X X) :
    restrict (M (σ 0)) (M (σ 1)) (M (σ 2)) (sidePermutation σ T) =
      sidePermutation σ (restrict (M 0) (M 1) (M 2) T) := by
  classical
  funext x y z
  let a : Fin 3 → Y := (Matrix.vecCons (x) (Matrix.vecCons (y) (Matrix.vecCons (z) Matrix.vecEmpty)))
  change restrict (M (σ 0)) (M (σ 1)) (M (σ 2)) (sidePermutation σ T)
      (a 0) (a 1) (a 2) =
    sidePermutation σ (restrict (M 0) (M 1) (M 2) T) (a 0) (a 1) (a 2)
  rw [sidePermutation_apply_coordinates]
  rw [restrict_eq_sum_coordinates (fun i => M (σ i))]
  rw [restrict_eq_sum_coordinates M T (fun i => a (σ.symm i))]
  rw [← (permuteCoordinates σ X).sum_comp
    (fun b => (∏ i, M i (a (σ.symm i)) (b i)) * T (b 0) (b 1) (b 2))]
  apply Finset.sum_congr rfl
  intro b hb
  rw [sidePermutation_apply_coordinates]
  change (∏ i, M (σ i) (a i) (b i)) *
      T (b (σ.symm 0)) (b (σ.symm 1)) (b (σ.symm 2)) =
    (∏ i, M i (a (σ.symm i)) (b (σ.symm i))) *
      T (b (σ.symm 0)) (b (σ.symm 1)) (b (σ.symm 2))
  congr 1
  simpa only [Equiv.symm_apply_apply] using
    Equiv.prod_comp σ (fun i => M i (a (σ.symm i)) (b (σ.symm i)))

end MatrixMultiplication.Foundation.Tensor

namespace MatrixMultiplication.AllFieldFiniteFamily.LocalMap

open MatrixMultiplication.Foundation

variable {F : Type*} [Field F] {X Y : Type} [Fintype X]
  {source : Tensor F X X X} {target : Tensor F Y Y Y}

def sidePermutation (σ : Equiv.Perm (Fin 3)) (map : LocalMap source target) :
    LocalMap (Tensor.sidePermutation σ source) (Tensor.sidePermutation σ target) where
  x := (Matrix.vecCons (map.x) (Matrix.vecCons (map.y) (Matrix.vecCons (map.z) Matrix.vecEmpty))) (σ 0)
  y := (Matrix.vecCons (map.x) (Matrix.vecCons (map.y) (Matrix.vecCons (map.z) Matrix.vecEmpty))) (σ 1)
  z := (Matrix.vecCons (map.x) (Matrix.vecCons (map.y) (Matrix.vecCons (map.z) Matrix.vecEmpty))) (σ 2)
  coefficient := by
    rw [Tensor.restrict_sidePermutation σ (Matrix.vecCons (map.x) (Matrix.vecCons (map.y) (Matrix.vecCons (map.z) Matrix.vecEmpty)))]
    change Tensor.sidePermutation σ (Tensor.restrict map.x map.y map.z source) = _
    rw [map.coefficient]

def restoreSides (σ : Equiv.Perm (Fin 3))
    (map : LocalMap (Tensor.sidePermutation σ source) (Tensor.sidePermutation σ target)) :
    LocalMap source target where
  x := (Matrix.vecCons (map.x) (Matrix.vecCons (map.y) (Matrix.vecCons (map.z) Matrix.vecEmpty))) (σ.symm 0)
  y := (Matrix.vecCons (map.x) (Matrix.vecCons (map.y) (Matrix.vecCons (map.z) Matrix.vecEmpty))) (σ.symm 1)
  z := (Matrix.vecCons (map.x) (Matrix.vecCons (map.y) (Matrix.vecCons (map.z) Matrix.vecEmpty))) (σ.symm 2)
  coefficient := by
    have h := Tensor.restrict_sidePermutation σ.symm (Matrix.vecCons (map.x) (Matrix.vecCons (map.y) (Matrix.vecCons (map.z) Matrix.vecEmpty)))
      (Tensor.sidePermutation σ source)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h
    rw [map.coefficient] at h
    simpa only [Tensor.sidePermutation_symm] using h

end MatrixMultiplication.AllFieldFiniteFamily.LocalMap

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.CWShapePhysicalPermutation

open MatrixMultiplication.Foundation CWStrands
open scoped BigOperators

variable {F : Type*} [CommRing F]

private theorem tensor_swapXY_inline_MatrixMultiplication_CWShapePhysicalPermutation (q : ℕ) (x y z : Fin (q + 2)) :
    FieldCW.tensor F q x y z = FieldCW.tensor F q y x z := by
  unfold FieldCW.tensor
  simp only [Finset.sum_add_distrib, mul_comm, mul_left_comm, mul_assoc]
  ring

private theorem tensor_swapYZ_inline_MatrixMultiplication_CWShapePhysicalPermutation (q : ℕ) (x y z : Fin (q + 2)) :
    FieldCW.tensor F q x y z = FieldCW.tensor F q x z y := by
  exact (FieldCW.tensor_cyclic F q x y z).trans
    ((tensor_swapXY_inline_MatrixMultiplication_CWShapePhysicalPermutation q y z x).trans (FieldCW.tensor_cyclic F q x z y).symm)

private theorem tensor_swapXZ_inline_MatrixMultiplication_CWShapePhysicalPermutation (q : ℕ) (x y z : Fin (q + 2)) :
    FieldCW.tensor F q x y z = FieldCW.tensor F q z y x := by
  exact (FieldCW.tensor_cyclic F q x y z).trans (tensor_swapXY_inline_MatrixMultiplication_CWShapePhysicalPermutation q y z x)

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
  · exact (tensor_swapYZ_inline_MatrixMultiplication_CWShapePhysicalPermutation q (a 0) (a 1) (a 2)).symm
  · exact (tensor_swapXY_inline_MatrixMultiplication_CWShapePhysicalPermutation q (a 0) (a 1) (a 2)).symm
  · exact (FieldCW.tensor_cyclic F q (a 0) (a 1) (a 2)).symm
  · exact FieldCW.tensor_cyclic F q (a 2) (a 0) (a 1)
  · exact (tensor_swapXZ_inline_MatrixMultiplication_CWShapePhysicalPermutation q (a 0) (a 1) (a 2)).symm

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
  let a : Fin 3 → P → Fin 7 := (Matrix.vecCons (x) (Matrix.vecCons (y) (Matrix.vecCons (z) Matrix.vecEmpty)))
  change Tensor.sidePermutation σ (shapeTensor P g) (a 0) (a 1) (a 2) =
    shapeTensor P (g ∘ σ) (a 0) (a 1) (a 2)
  rw [Tensor.sidePermutation_apply_coordinates]
  have h := shapeTensor_permute (F := F) σ g (fun s => a (σ.symm s))
  simpa only [Equiv.symm_apply_apply] using h.symm

end MatrixMultiplication.CWShapePhysicalPermutation

end

end MatrixAllFields

end OAI
