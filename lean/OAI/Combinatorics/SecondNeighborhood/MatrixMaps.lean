import OAI.Combinatorics.SecondNeighborhood.PruningDefinitions
import Mathlib.Data.Matrix.Mul
import Mathlib.Basic.Real.Basic

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

variable {V : Type*}

def SupportedCoefficients (r : V → V → Prop) (a : V → V → ℝ) : Prop :=
  ∀ x y, ¬ r x y → a x y = 0

theorem SupportedCoefficients.of_ne_zero {r : V → V → Prop}
    {a : V → V → ℝ} (ha : SupportedCoefficients r a) {x y : V}
    (hxy : a x y ≠ 0) : r x y := by
  by_contra h
  exact hxy (ha x y h)

variable [Fintype V] [DecidableEq V]

noncomputable section

def matrixL (r : V → V → Prop) (R C : Finset (V × V)) (a : V → V → ℝ) :
    Matrix ↥(Z r R C) ↥R ℝ :=
  Matrix.of fun z left => if z.val.2 = left.val.2 then a left.val.1 z.val.1 else 0

def matrixN (r : V → V → Prop) (R C : Finset (V × V)) (b : V → V → ℝ) :
    Matrix ↥C ↥(Z r R C) ℝ :=
  Matrix.of fun right z => if right.val.1 = z.val.1 then b right.val.2 z.val.2 else 0

def matrixB (r : V → V → Prop) (R C : Finset (V × V)) (b : V → V → ℝ) :
    Matrix ↥(H r R C) ↥R ℝ :=
  Matrix.of fun h left => if h.val.1 = left.val.1 then b h.val.2 left.val.2 else 0

def matrixA (r : V → V → Prop) (R C : Finset (V × V)) (a : V → V → ℝ) :
    Matrix ↥C ↥(H r R C) ℝ :=
  Matrix.of fun right h => if right.val.2 = h.val.2 then a h.val.1 right.val.1 else 0

@[simp] theorem matrixL_apply (r : V → V → Prop) (R C : Finset (V × V))
    (a : V → V → ℝ) (z : ↥(Z r R C)) (left : ↥R) :
    matrixL r R C a z left =
      if z.val.2 = left.val.2 then a left.val.1 z.val.1 else 0 := rfl

@[simp] theorem matrixN_apply (r : V → V → Prop) (R C : Finset (V × V))
    (b : V → V → ℝ) (right : ↥C) (z : ↥(Z r R C)) :
    matrixN r R C b right z =
      if right.val.1 = z.val.1 then b right.val.2 z.val.2 else 0 := rfl

@[simp] theorem matrixB_apply (r : V → V → Prop) (R C : Finset (V × V))
    (b : V → V → ℝ) (h : ↥(H r R C)) (left : ↥R) :
    matrixB r R C b h left =
      if h.val.1 = left.val.1 then b h.val.2 left.val.2 else 0 := rfl

@[simp] theorem matrixA_apply (r : V → V → Prop) (R C : Finset (V × V))
    (a : V → V → ℝ) (right : ↥C) (h : ↥(H r R C)) :
    matrixA r R C a right h =
      if right.val.2 = h.val.2 then a h.val.1 right.val.1 else 0 := rfl

end
end SeymourSecondNeighborhood.Pruning

end OAI
