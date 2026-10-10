import OAI.GroupTheory.PolycyclicRecognition.Finiteness.AbelianSecondHomologyPairing
import Mathlib.LinearAlgebra.ExteriorPower.Basic

namespace OAI

/-! # The alternating exterior-square pairing used on abelian bar cycles -/

noncomputable section
namespace PolycyclicRecognition
variable {M : Type} [AddCommGroup M]

def exteriorSquareValue (x y : M) : ⋀[ℤ]^2 M :=
  exteriorPower.ιMulti ℤ 2 ![x, y]

theorem exteriorSquareValue_swap (x y : M) :
    exteriorSquareValue y x = -exteriorSquareValue x y := by
  have h := (exteriorPower.ιMulti ℤ 2 (M := M)).map_swap ![x, y]
    (i := 0) (j := 1) (by decide)
  have he : ![x, y] ∘ Equiv.swap (0 : Fin 2) 1 = ![y, x] := by
    funext i
    fin_cases i <;> simp
  rw [he] at h
  exact h

theorem exteriorSquareValue_add_left (x y z : M) :
    exteriorSquareValue (x + y) z = exteriorSquareValue x z + exteriorSquareValue y z :=
  (exteriorPower.ιMulti ℤ 2).map_vecCons_add ![z] x y

theorem exteriorSquareValue_add_right (x y z : M) :
    exteriorSquareValue x (y + z) = exteriorSquareValue x y + exteriorSquareValue x z := by
  rw [exteriorSquareValue_swap, exteriorSquareValue_add_left,
    exteriorSquareValue_swap y x, exteriorSquareValue_swap z x]
  abel

@[simp] theorem exteriorSquareValue_zero_left (x : M) : exteriorSquareValue 0 x = 0 :=
  (exteriorPower.ιMulti ℤ 2).map_coord_zero (0 : Fin 2) rfl

@[simp] theorem exteriorSquareValue_zero_right (x : M) : exteriorSquareValue x 0 = 0 := by
  rw [exteriorSquareValue_swap, exteriorSquareValue_zero_left, neg_zero]

def exteriorSquarePairing : M →+ M →+ ⋀[ℤ]^2 M where
  toFun x :=
    { toFun := exteriorSquareValue x
      map_zero' := exteriorSquareValue_zero_right x
      map_add' := exteriorSquareValue_add_right x }
  map_zero' := by
    apply AddMonoidHom.ext
    intro x
    exact exteriorSquareValue_zero_left x
  map_add' x y := by
    apply AddMonoidHom.ext
    intro z
    exact exteriorSquareValue_add_left x y z

@[simp] theorem exteriorSquarePairing_apply (x y : M) :
    exteriorSquarePairing x y = exteriorSquareValue x y := rfl

end PolycyclicRecognition

end

end OAI
