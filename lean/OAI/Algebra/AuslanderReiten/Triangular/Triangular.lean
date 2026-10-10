import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Finiteness.Prod

namespace OAI

namespace ArExplicit

@[ext] structure Triangular (R F : Type*) where
  top : R
  bottom : R
  off : F

namespace Triangular

variable {R F : Type*}

def coordinates : Triangular R F ≃ (R × R) × F where
  toFun x := ((x.top, x.bottom), x.off)
  invFun x := ⟨x.1.1, x.1.2, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [AddCommGroup R] [AddCommGroup F] : AddCommGroup (Triangular R F) :=
  coordinates.addCommGroup

def coordinateAddEquiv [AddCommGroup R] [AddCommGroup F] :
    Triangular R F ≃+ (R × R) × F where
  toEquiv := coordinates
  map_add' _ _ := rfl

variable [Ring R] [AddCommGroup F]
variable [Module R F] [Module Rᵐᵒᵖ F]

instance : One (Triangular R F) := ⟨⟨1, 1, 0⟩⟩

instance : Mul (Triangular R F) :=
  ⟨fun x y => ⟨x.top * y.top, x.bottom * y.bottom,
    x.bottom • y.off + MulOpposite.op y.top • x.off⟩⟩

section BasicCoordinates

omit [Module R F] [Module Rᵐᵒᵖ F]

@[simp] theorem top_zero : (0 : Triangular R F).top = 0 := rfl
@[simp] theorem bottom_zero : (0 : Triangular R F).bottom = 0 := rfl
@[simp] theorem off_zero : (0 : Triangular R F).off = 0 := rfl
@[simp] theorem top_one : (1 : Triangular R F).top = 1 := rfl
@[simp] theorem bottom_one : (1 : Triangular R F).bottom = 1 := rfl
@[simp] theorem off_one : (1 : Triangular R F).off = 0 := rfl
@[simp] theorem top_add (x y : Triangular R F) : (x + y).top = x.top + y.top := rfl
@[simp] theorem bottom_add (x y : Triangular R F) :
    (x + y).bottom = x.bottom + y.bottom := rfl
@[simp] theorem off_add (x y : Triangular R F) : (x + y).off = x.off + y.off := rfl
end BasicCoordinates

@[simp] theorem top_mul (x y : Triangular R F) : (x * y).top = x.top * y.top := rfl
@[simp] theorem bottom_mul (x y : Triangular R F) :
    (x * y).bottom = x.bottom * y.bottom := rfl
@[simp] theorem off_mul (x y : Triangular R F) :
    (x * y).off = x.bottom • y.off + MulOpposite.op y.top • x.off := rfl

variable [SMulCommClass R Rᵐᵒᵖ F]

instance : Ring (Triangular R F) where
  __ := (inferInstance : AddCommGroup (Triangular R F))
  mul_assoc x y z := by
    ext
    · exact mul_assoc ..
    · exact mul_assoc ..
    · simp only [off_mul, bottom_mul, top_mul, mul_smul, smul_add, MulOpposite.op_mul]
      rw [← smul_comm x.bottom (MulOpposite.op z.top) y.off]
      exact (add_assoc ..).symm
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  left_distrib x y z := by ext <;> simp [mul_add, smul_add, add_smul, add_add_add_comm]
  right_distrib x y z := by ext <;> simp [add_mul, smul_add, add_smul, add_add_add_comm]
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp

def diagonal : Triangular R F →+* R × R where
  toFun x := (x.top, x.bottom)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem diagonal_surjective : Function.Surjective (diagonal (R := R) (F := F)) := by
  intro x
  exact ⟨⟨x.1, x.2, 0⟩, rfl⟩

def offDiagonal (f : F) : Triangular R F := ⟨0, 0, f⟩

@[simp] theorem offDiagonal_mul_offDiagonal (f g : F) :
    offDiagonal (R := R) f * offDiagonal g = 0 := by
  ext <;> simp [offDiagonal]

section Scalars

variable (k : Type*) [CommRing k] [Algebra k R] [Module k F]

instance : Module k (Triangular R F) := coordinateAddEquiv.module k

@[simp] theorem top_smul (c : k) (x : Triangular R F) : (c • x).top = c • x.top := rfl
@[simp] theorem bottom_smul (c : k) (x : Triangular R F) :
    (c • x).bottom = c • x.bottom := rfl
@[simp] theorem off_smul (c : k) (x : Triangular R F) : (c • x).off = c • x.off := rfl

variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass k Rᵐᵒᵖ F]

instance : Algebra k (Triangular R F) := Algebra.ofModule
  (by
    intro c x y
    ext
    · exact smul_mul_assoc c x.top y.top
    · exact smul_mul_assoc c x.bottom y.bottom
    · simp only [off_mul, off_smul, bottom_smul, smul_assoc, smul_add]
      rw [← smul_comm c (MulOpposite.op y.top) x.off])
  (by
    intro c x y
    ext
    · exact mul_smul_comm c x.top y.top
    · exact mul_smul_comm c x.bottom y.bottom
    · simp only [off_mul, off_smul, top_smul, MulOpposite.op_smul,
        smul_assoc, smul_add]
      rw [← smul_comm c x.bottom y.off])

def coordinateLinearEquiv : Triangular R F ≃ₗ[k] (R × R) × F :=
  (coordinateAddEquiv (R := R) (F := F)).linearEquiv k

instance [Module.Finite k R] [Module.Finite k F] : Module.Finite k (Triangular R F) :=
  Module.Finite.equiv (coordinateLinearEquiv (R := R) (F := F) k).symm

end Scalars

end Triangular
end ArExplicit

end OAI
