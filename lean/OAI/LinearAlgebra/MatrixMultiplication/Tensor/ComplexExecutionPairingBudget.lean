import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialKernelExecution
import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexInitialTargetExecution
import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexBalancedSeparation
import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.ComplexCWLocalConstruction

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

namespace MatrixMultiplication.Foundation.ExecutionPairingBudget

open scoped BigOperators
open Tensor PolynomialKernelExecution BalancedSeparation LabelHierarchySeparation

structure MatrixCoordinates (PX PY PZ : Type*) where
  rows : ℕ
  inner : ℕ
  columns : ℕ
  left : PX ≃ (Fin rows × Fin inner)
  middle : PY ≃ (Fin inner × Fin columns)
  right : PZ ≃ (Fin columns × Fin rows)

namespace MatrixCoordinates

variable {PX PY PZ NX NY NZ : Type*}

def volume (shape : MatrixCoordinates PX PY PZ) : ℕ :=
  shape.rows * shape.inner * shape.columns

def Positive (shape : MatrixCoordinates PX PY PZ) : Prop :=
  0 < shape.rows ∧ 0 < shape.inner ∧ 0 < shape.columns

def tensor (shape : MatrixCoordinates PX PY PZ) : Tensor ℂ PX PY PZ :=
  Tensor.pullback shape.left shape.middle shape.right
    (matrixCoefficients (Fin shape.rows) (Fin shape.inner) (Fin shape.columns))

theorem left_card [Fintype PX] (shape : MatrixCoordinates PX PY PZ) :
    Fintype.card PX = shape.rows * shape.inner := by
  simpa only [Fintype.card_prod, Fintype.card_fin] using Fintype.card_congr shape.left

theorem middle_card [Fintype PY] (shape : MatrixCoordinates PX PY PZ) :
    Fintype.card PY = shape.inner * shape.columns := by
  simpa only [Fintype.card_prod, Fintype.card_fin] using Fintype.card_congr shape.middle

theorem right_card [Fintype PZ] (shape : MatrixCoordinates PX PY PZ) :
    Fintype.card PZ = shape.columns * shape.rows := by
  simpa only [Fintype.card_prod, Fintype.card_fin] using Fintype.card_congr shape.right

def standard (a b c : ℕ) :
    MatrixCoordinates (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) where
  rows := a
  inner := b
  columns := c
  left := Equiv.refl _
  middle := Equiv.refl _
  right := Equiv.refl _

@[simp] theorem standard_volume (a b c : ℕ) : (standard a b c).volume = a * b * c := rfl

@[simp] theorem standard_tensor (a b c : ℕ) :
    (standard a b c).tensor = matrixCoefficients (K := ℂ) (Fin a) (Fin b) (Fin c) := rfl

def scalar : MatrixCoordinates Unit Unit Unit where
  rows := 1
  inner := 1
  columns := 1
  left := singlePairingZ.symm
  middle := singlePairingZ.symm
  right := singlePairingZ.symm

@[simp] theorem scalar_volume : scalar.volume = 1 := rfl

theorem scalar_positive : scalar.Positive := by
  exact ⟨Nat.zero_lt_one, Nat.zero_lt_one, Nat.zero_lt_one⟩

@[simp] theorem scalar_tensor : scalar.tensor = fun _ _ _ => (1 : ℂ) := by
  funext x y z
  rfl

def pairProductEquiv (a b c d : ℕ) :
    ((Fin a × Fin b) × (Fin c × Fin d)) ≃ (Fin (a * c) × Fin (b * d)) :=
  (Equiv.prodProdProdComm (Fin a) (Fin b) (Fin c) (Fin d)).trans
    (Equiv.prodCongr (@finProdFinEquiv a c) (@finProdFinEquiv b d))

@[simp] theorem pairProductEquiv_apply (a b c d : ℕ)
    (x : (Fin a × Fin b) × (Fin c × Fin d)) :
    pairProductEquiv a b c d x =
      (finProdFinEquiv (x.1.1, x.2.1), finProdFinEquiv (x.1.2, x.2.2)) := rfl

def product (old : MatrixCoordinates PX PY PZ) (new : MatrixCoordinates NX NY NZ) :
    MatrixCoordinates (PX × NX) (PY × NY) (PZ × NZ) where
  rows := old.rows * new.rows
  inner := old.inner * new.inner
  columns := old.columns * new.columns
  left := (Equiv.prodCongr old.left new.left).trans
    (pairProductEquiv old.rows old.inner new.rows new.inner)
  middle := (Equiv.prodCongr old.middle new.middle).trans
    (pairProductEquiv old.inner old.columns new.inner new.columns)
  right := (Equiv.prodCongr old.right new.right).trans
    (pairProductEquiv old.columns old.rows new.columns new.rows)

@[simp] theorem product_volume (old : MatrixCoordinates PX PY PZ)
    (new : MatrixCoordinates NX NY NZ) :
    (product old new).volume = old.volume * new.volume := by
  simp only [volume, product]
  ring

theorem product_positive (old : MatrixCoordinates PX PY PZ)
    (new : MatrixCoordinates NX NY NZ) (hold : old.Positive) (hnew : new.Positive) :
    (product old new).Positive :=
  ⟨Nat.mul_pos hold.1 hnew.1, Nat.mul_pos hold.2.1 hnew.2.1,
    Nat.mul_pos hold.2.2 hnew.2.2⟩

theorem product_tensor (old : MatrixCoordinates PX PY PZ)
    (new : MatrixCoordinates NX NY NZ) :
    (product old new).tensor = Tensor.product old.tensor new.tensor := by
  funext x y z
  have h := matrixCoefficients_product (K := ℂ)
    (((old.left x.1).1, (new.left x.2).1), ((old.left x.1).2, (new.left x.2).2))
    (((old.middle y.1).1, (new.middle y.2).1),
      ((old.middle y.1).2, (new.middle y.2).2))
    (((old.right z.1).1, (new.right z.2).1),
      ((old.right z.1).2, (new.right z.2).2))
  change matrixCoefficients (K := ℂ) (Fin (old.rows * new.rows))
    (Fin (old.inner * new.inner)) (Fin (old.columns * new.columns))
    (finProdFinEquiv ((old.left x.1).1, (new.left x.2).1),
      finProdFinEquiv ((old.left x.1).2, (new.left x.2).2))
    (finProdFinEquiv ((old.middle y.1).1, (new.middle y.2).1),
      finProdFinEquiv ((old.middle y.1).2, (new.middle y.2).2))
    (finProdFinEquiv ((old.right z.1).1, (new.right z.2).1),
      finProdFinEquiv ((old.right z.1).2, (new.right z.2).2)) = _
  simpa only [tensor, product, Tensor.pullback, Tensor.product,
    Equiv.trans_apply, Equiv.prodCongr_apply, pairProductEquiv_apply,
    matrixCoefficients, Equiv.apply_eq_iff_eq] using h.symm

section Banks

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {PX PY PZ : I → Type*}

def bankIndexEquiv (dimension : I → ℕ) :
    (∀ i, Fin (dimension i)) ≃ Fin (∏ i, dimension i) :=
  Fintype.equivFinOfCardEq (by simp only [Fintype.card_pi, Fintype.card_fin])

def bank (shape : ∀ i, MatrixCoordinates (PX i) (PY i) (PZ i)) :
    MatrixCoordinates (∀ i, PX i) (∀ i, PY i) (∀ i, PZ i) where
  rows := ∏ i, (shape i).rows
  inner := ∏ i, (shape i).inner
  columns := ∏ i, (shape i).columns
  left := (Equiv.piCongrRight (fun i => (shape i).left)).trans
    ((piPairEquiv (fun i => Fin (shape i).rows) (fun i => Fin (shape i).inner)).symm.trans
      (Equiv.prodCongr (bankIndexEquiv (fun i => (shape i).rows))
        (bankIndexEquiv (fun i => (shape i).inner))))
  middle := (Equiv.piCongrRight (fun i => (shape i).middle)).trans
    ((piPairEquiv (fun i => Fin (shape i).inner) (fun i => Fin (shape i).columns)).symm.trans
      (Equiv.prodCongr (bankIndexEquiv (fun i => (shape i).inner))
        (bankIndexEquiv (fun i => (shape i).columns))))
  right := (Equiv.piCongrRight (fun i => (shape i).right)).trans
    ((piPairEquiv (fun i => Fin (shape i).columns) (fun i => Fin (shape i).rows)).symm.trans
      (Equiv.prodCongr (bankIndexEquiv (fun i => (shape i).columns))
        (bankIndexEquiv (fun i => (shape i).rows))))

@[simp] theorem bank_volume (shape : ∀ i, MatrixCoordinates (PX i) (PY i) (PZ i)) :
    (bank shape).volume = ∏ i, (shape i).volume := by
  simp only [bank, volume, Finset.prod_mul_distrib]

theorem bank_positive (shape : ∀ i, MatrixCoordinates (PX i) (PY i) (PZ i))
    (positive : ∀ i, (shape i).Positive) : (bank shape).Positive :=
  ⟨Finset.prod_pos (fun i _ => (positive i).1),
    Finset.prod_pos (fun i _ => (positive i).2.1),
    Finset.prod_pos (fun i _ => (positive i).2.2)⟩

theorem bank_tensor (shape : ∀ i, MatrixCoordinates (PX i) (PY i) (PZ i)) :
    (bank shape).tensor = bankTensor (fun i => (shape i).tensor) := by
  funext x y z
  have h := congrFun (congrFun (congrFun
    (matrixBank_identity (K := ℂ)
      (A := fun i => Fin (shape i).rows) (B := fun i => Fin (shape i).inner)
      (C := fun i => Fin (shape i).columns))
    ((fun i => ((shape i).left (x i)).1), (fun i => ((shape i).left (x i)).2)))
    ((fun i => ((shape i).middle (y i)).1), (fun i => ((shape i).middle (y i)).2)))
    ((fun i => ((shape i).right (z i)).1), (fun i => ((shape i).right (z i)).2))
  change matrixCoefficients (K := ℂ) (Fin (∏ i, (shape i).rows))
    (Fin (∏ i, (shape i).inner)) (Fin (∏ i, (shape i).columns))
    (bankIndexEquiv (fun i => (shape i).rows) (fun i => ((shape i).left (x i)).1),
      bankIndexEquiv (fun i => (shape i).inner) (fun i => ((shape i).left (x i)).2))
    (bankIndexEquiv (fun i => (shape i).inner) (fun i => ((shape i).middle (y i)).1),
      bankIndexEquiv (fun i => (shape i).columns) (fun i => ((shape i).middle (y i)).2))
    (bankIndexEquiv (fun i => (shape i).columns) (fun i => ((shape i).right (z i)).1),
      bankIndexEquiv (fun i => (shape i).rows) (fun i => ((shape i).right (z i)).2)) = _
  simp only [tensor, Tensor.pullback, bankTensor, piPairEquiv, Equiv.coe_fn_mk,
    matrixCoefficients, Equiv.apply_eq_iff_eq] at h ⊢
  refine Eq.trans ?_ (Eq.trans h.symm ?_)
  · apply -synthAssignedInstances @if_congr <;> rfl
  · apply Finset.prod_congr rfl
    intro i _
    apply -synthAssignedInstances @if_congr <;> rfl

theorem bank_budget (shape : ∀ i, MatrixCoordinates (PX i) (PY i) (PZ i))
    (rankBound : I → ℕ) (budget : ∀ i, (shape i).volume ≤ rankBound i) :
    (bank shape).volume ≤ ∏ i, rankBound i := by
  rw [bank_volume]
  exact Finset.prod_le_prod (fun i _ => budget i)

end Banks
end MatrixCoordinates

section Execution

variable {X Y Z Prefix PX PY PZ AX AY AZ : Type*}
variable [Fintype AX] [Fintype AY] [Fintype AZ]
variable {support : X → Y → Z → Prop}
variable (E : Execution X Y Z Prefix PX PY PZ AX AY AZ support)
variable {New NX NY NZ BX BY BZ : Type*}
variable [Fintype BX] [Fintype BY] [Fintype BZ]
variable (S : Stage E New NX NY NZ BX BY BZ)

theorem step_budget (old : MatrixCoordinates PX PY PZ) (new : MatrixCoordinates NX NY NZ)
    (previous : old.volume ≤ E.rankBound) (current : new.volume ≤ S.rankBound) :
    (old.product new).volume ≤ (E.step S).rankBound := by
  rw [MatrixCoordinates.product_volume, Execution.step_rankBound]
  exact Nat.mul_le_mul previous current

end Execution

section Initial

variable {X Y Z RawLabel Label : Type*}

theorem initial_budget (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (lx : X → RawLabel) (ly : Y → RawLabel) (lz : Z → RawLabel)
    (embed : Label → RawLabel) (injective : Function.Injective embed)
    (support : X → Y → Z → Prop)
    (compatible : ∀ x y z, support x y z → PX x → PY y → PZ z →
      lx x = ly y ∧ lx x = lz z) :
    MatrixCoordinates.scalar.volume ≤
      (InitialTargetExecution.initial PX PY PZ lx ly lz embed injective support compatible).rankBound := by
  exact le_rfl

end Initial

section PrimitiveBanks

open CWLocalConstruction

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {AX AY AZ Label : I → Type*}
variable [∀ i, Fintype (AX i)] [∀ i, Fintype (AY i)] [∀ i, Fintype (AZ i)]
variable [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]
variable (m a b c : I → ℕ)
variable (P : ∀ i, CWPrimitive (AX := AX i) (AY := AY i) (AZ := AZ i) (Label := Label i)
  (m i) (a i) (b i) (c i))
variable (physical : ∀ i, Site (m i) → OrientationRates.Orientation)

def primitiveBankCoordinates : MatrixCoordinates
    (∀ i, Fin (a i) × Fin (b i)) (∀ i, Fin (b i) × Fin (c i))
    (∀ i, Fin (c i) × Fin (a i)) :=
  MatrixCoordinates.bank (fun i => MatrixCoordinates.standard (a i) (b i) (c i))

include P in

theorem primitive_bank_positive : (primitiveBankCoordinates a b c).Positive := by
  exact MatrixCoordinates.bank_positive _ (fun i =>
    ⟨(P i).leftDim_pos, (P i).middleDim_pos, (P i).rightDim_pos⟩)

theorem admissible_bank_budget
    (admissible : ∀ i, Admissible (P i) (physical i)) :
    (primitiveBankCoordinates a b c).volume ≤ ∏ i, (P i).rankBound := by
  exact MatrixCoordinates.bank_budget _ _ (fun i => (admissible i).pairing_budget)

end PrimitiveBanks

end MatrixMultiplication.Foundation.ExecutionPairingBudget

end

end OAI
