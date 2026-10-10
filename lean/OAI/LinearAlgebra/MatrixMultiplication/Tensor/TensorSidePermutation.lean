import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.FiniteFamily
import Mathlib.Tactic.FinCases

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation.Tensor

variable {K X Y : Type*}

def sidePermutation (σ : Equiv.Perm (Fin 3)) (T : Tensor K X X X) :
    Tensor K X X X :=
  fun x y z => T (![x, y, z] (σ.symm 0))
    (![x, y, z] (σ.symm 1)) (![x, y, z] (σ.symm 2))

private theorem coordinates_eta (a : Fin 3 → X) : ![a 0, a 1, a 2] = a := by
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
  let a : Fin 3 → X := ![x, y, z]
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
  toFun a := ![a.1, a.2.1, a.2.2]
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
  have h := (coordinatesEquiv X).sum_comp
    (fun b => (∏ i, M i (a i) (b i)) * T (b 0) (b 1) (b 2))
  change (∑ b : X × X × X,
    (∏ i, M i (a i) (![b.1, b.2.1, b.2.2] i)) * T b.1 b.2.1 b.2.2) = _ at h
  simpa [restrict, Fintype.sum_prod_type, Fin.prod_univ_three] using h

theorem restrict_sidePermutation (σ : Equiv.Perm (Fin 3))
    (M : Fin 3 → Y → X → K) (T : Tensor K X X X) :
    restrict (M (σ 0)) (M (σ 1)) (M (σ 2)) (sidePermutation σ T) =
      sidePermutation σ (restrict (M 0) (M 1) (M 2) T) := by
  classical
  funext x y z
  let a : Fin 3 → Y := ![x, y, z]
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
  x := ![map.x, map.y, map.z] (σ 0)
  y := ![map.x, map.y, map.z] (σ 1)
  z := ![map.x, map.y, map.z] (σ 2)
  coefficient := by
    rw [Tensor.restrict_sidePermutation σ ![map.x, map.y, map.z]]
    change Tensor.sidePermutation σ (Tensor.restrict map.x map.y map.z source) = _
    rw [map.coefficient]

def restoreSides (σ : Equiv.Perm (Fin 3))
    (map : LocalMap (Tensor.sidePermutation σ source) (Tensor.sidePermutation σ target)) :
    LocalMap source target where
  x := ![map.x, map.y, map.z] (σ.symm 0)
  y := ![map.x, map.y, map.z] (σ.symm 1)
  z := ![map.x, map.y, map.z] (σ.symm 2)
  coefficient := by
    have h := Tensor.restrict_sidePermutation σ.symm ![map.x, map.y, map.z]
      (Tensor.sidePermutation σ source)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h
    rw [map.coefficient] at h
    simpa only [Tensor.sidePermutation_symm] using h

end MatrixMultiplication.AllFieldFiniteFamily.LocalMap

end OAI
