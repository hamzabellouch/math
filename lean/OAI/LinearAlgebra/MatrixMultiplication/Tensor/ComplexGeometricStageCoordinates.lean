import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexExecutionPairingBudget

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

namespace MatrixMultiplication.Foundation.GeometricStageCoordinates

open Tensor BalancedSeparation LabelHierarchySeparation ExecutionPairingBudget

def scalarPair : PUnit ≃ (Fin 1 × Fin 1) where
  toFun _ := (0, 0)
  invFun _ := PUnit.unit
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

def xy (k : ℕ) : MatrixCoordinates (Fin k) (Fin k) PUnit where
  rows := 1
  inner := k
  columns := 1
  left := (singlePairingX k).symm
  middle := (singlePairingY k).symm
  right := scalarPair

def xz (k : ℕ) : MatrixCoordinates (Fin k) PUnit (Fin k) where
  rows := k
  inner := 1
  columns := 1
  left := (singlePairingY k).symm
  middle := scalarPair
  right := (singlePairingX k).symm

def yz (k : ℕ) : MatrixCoordinates PUnit (Fin k) (Fin k) where
  rows := 1
  inner := 1
  columns := k
  left := scalarPair
  middle := (singlePairingX k).symm
  right := (singlePairingY k).symm

@[simp] theorem xy_tensor_apply (k : ℕ) (x y : Fin k) (z : PUnit) :
    (xy k).tensor x y z = if x = y then 1 else 0 := by
  change (if x = y ∧ (0 : Fin 1) = 0 ∧ (0 : Fin 1) = 0 then (1 : ℂ) else 0) = _
  simp

@[simp] theorem xz_tensor_apply (k : ℕ) (x : Fin k) (y : PUnit) (z : Fin k) :
    (xz k).tensor x y z = if x = z then 1 else 0 := by
  change (if (0 : Fin 1) = 0 ∧ (0 : Fin 1) = 0 ∧ z = x then (1 : ℂ) else 0) = _
  simp [eq_comm]

@[simp] theorem yz_tensor_apply (k : ℕ) (x : PUnit) (y z : Fin k) :
    (yz k).tensor x y z = if y = z then 1 else 0 := by
  change (if (0 : Fin 1) = 0 ∧ y = z ∧ (0 : Fin 1) = 0 then (1 : ℂ) else 0) = _
  simp

theorem xy_tensor_eq_one_iff (k : ℕ) (x y : Fin k) (z : PUnit) :
    (xy k).tensor x y z = 1 ↔ x = y := by
  rw [xy_tensor_apply]
  split_ifs with h <;> simp [h]

theorem xz_tensor_eq_one_iff (k : ℕ) (x : Fin k) (y : PUnit) (z : Fin k) :
    (xz k).tensor x y z = 1 ↔ x = z := by
  rw [xz_tensor_apply]
  split_ifs with h <;> simp [h]

theorem yz_tensor_eq_one_iff (k : ℕ) (x : PUnit) (y z : Fin k) :
    (yz k).tensor x y z = 1 ↔ y = z := by
  rw [yz_tensor_apply]
  split_ifs with h <;> simp [h]

theorem xy_tensor_ne_zero_iff (k : ℕ) (x y : Fin k) (z : PUnit) :
    (xy k).tensor x y z ≠ 0 ↔ x = y := by
  rw [xy_tensor_apply]
  split_ifs with h <;> simp [h]

theorem xz_tensor_ne_zero_iff (k : ℕ) (x : Fin k) (y : PUnit) (z : Fin k) :
    (xz k).tensor x y z ≠ 0 ↔ x = z := by
  rw [xz_tensor_apply]
  split_ifs with h <;> simp [h]

theorem yz_tensor_ne_zero_iff (k : ℕ) (x : PUnit) (y z : Fin k) :
    (yz k).tensor x y z ≠ 0 ↔ y = z := by
  rw [yz_tensor_apply]
  split_ifs with h <;> simp [h]

@[simp] theorem xy_volume (k : ℕ) : (xy k).volume = k := by
  simp [MatrixCoordinates.volume, xy]

@[simp] theorem xz_volume (k : ℕ) : (xz k).volume = k := by
  simp [MatrixCoordinates.volume, xz]

@[simp] theorem yz_volume (k : ℕ) : (yz k).volume = k := by
  simp [MatrixCoordinates.volume, yz]

theorem xy_positive {k : ℕ} (hk : 0 < k) : (xy k).Positive :=
  ⟨Nat.zero_lt_one, hk, Nat.zero_lt_one⟩

theorem xz_positive {k : ℕ} (hk : 0 < k) : (xz k).Positive :=
  ⟨hk, Nat.zero_lt_one, Nat.zero_lt_one⟩

theorem yz_positive {k : ℕ} (hk : 0 < k) : (yz k).Positive :=
  ⟨Nat.zero_lt_one, Nat.zero_lt_one, hk⟩

theorem xy_budget (k : ℕ) : (xy k).volume ≤ poolAuxiliaryCost k := by
  simpa only [xy_volume] using population_le_poolAuxiliaryCost k

theorem xz_budget (k : ℕ) : (xz k).volume ≤ poolAuxiliaryCost k := by
  simpa only [xz_volume] using population_le_poolAuxiliaryCost k

theorem yz_budget (k : ℕ) : (yz k).volume ≤ poolAuxiliaryCost k := by
  simpa only [yz_volume] using population_le_poolAuxiliaryCost k

def fiveStage (k0 k1 k2 k3 k4 : ℕ) :=
  ((((MatrixCoordinates.scalar.product (xy k0)).product (xz k1)).product (yz k2)).product
    (yz k3)).product (xy k4)

theorem fiveStage_dimensions (k0 k1 k2 k3 k4 : ℕ) :
    (fiveStage k0 k1 k2 k3 k4).rows = k1 ∧
      (fiveStage k0 k1 k2 k3 k4).inner = k0 * k4 ∧
      (fiveStage k0 k1 k2 k3 k4).columns = k2 * k3 := by
  simp [fiveStage, MatrixCoordinates.product, MatrixCoordinates.scalar, xy, xz, yz]

@[simp] theorem fiveStage_volume (k0 k1 k2 k3 k4 : ℕ) :
    (fiveStage k0 k1 k2 k3 k4).volume = k0 * k1 * k2 * k3 * k4 := by
  simp only [fiveStage, MatrixCoordinates.product_volume, MatrixCoordinates.scalar_volume,
    xy_volume, xz_volume, yz_volume, one_mul]

theorem fiveStage_positive {k0 k1 k2 k3 k4 : ℕ}
    (h0 : 0 < k0) (h1 : 0 < k1) (h2 : 0 < k2) (h3 : 0 < k3) (h4 : 0 < k4) :
    (fiveStage k0 k1 k2 k3 k4).Positive := by
  have hstart := MatrixCoordinates.product_positive MatrixCoordinates.scalar (xy k0)
    MatrixCoordinates.scalar_positive (xy_positive h0)
  have h01 := MatrixCoordinates.product_positive _ (xz k1) hstart (xz_positive h1)
  have h012 := MatrixCoordinates.product_positive _ (yz k2) h01 (yz_positive h2)
  have h0123 := MatrixCoordinates.product_positive _ (yz k3) h012 (yz_positive h3)
  exact MatrixCoordinates.product_positive _ (xy k4) h0123 (xy_positive h4)

theorem fiveStage_budget (k0 k1 k2 k3 k4 : ℕ) :
    (fiveStage k0 k1 k2 k3 k4).volume ≤
      poolAuxiliaryCost k0 * poolAuxiliaryCost k1 * poolAuxiliaryCost k2 *
        poolAuxiliaryCost k3 * poolAuxiliaryCost k4 := by
  rw [fiveStage_volume]
  exact Nat.mul_le_mul
    (Nat.mul_le_mul
      (Nat.mul_le_mul
        (Nat.mul_le_mul (population_le_poolAuxiliaryCost k0)
          (population_le_poolAuxiliaryCost k1))
        (population_le_poolAuxiliaryCost k2))
      (population_le_poolAuxiliaryCost k3))
    (population_le_poolAuxiliaryCost k4)

theorem fiveStage_tensor (k0 k1 k2 k3 k4 : ℕ) :
    (fiveStage k0 k1 k2 k3 k4).tensor =
      Tensor.product
        (Tensor.product
          (Tensor.product
            (Tensor.product (Tensor.product MatrixCoordinates.scalar.tensor (xy k0).tensor)
              (xz k1).tensor)
            (yz k2).tensor)
          (yz k3).tensor)
        (xy k4).tensor := by
  simp only [fiveStage, MatrixCoordinates.product_tensor]

end MatrixMultiplication.Foundation.GeometricStageCoordinates

end

end OAI
