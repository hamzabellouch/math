import Mathlib.Basic.Complex.Basic
import OAI.Algebra.Finitistic.Selection.MatrixModel

namespace OAI
namespace LittleFinitistic

noncomputable def parityValue (a : ZMod 2) : ℂˣ := if a = 0 then 1 else -1

@[simp] theorem parityValue_zero : parityValue 0 = 1 := by simp [parityValue]
@[simp] theorem parityValue_one : parityValue 1 = -1 := by norm_num [parityValue]

theorem parityValue_add (a b : ZMod 2) : parityValue (a+b) = parityValue a * parityValue b := by
  have hc : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hc a with rfl | rfl <;> rcases hc b with rfl | rfl
  · simp
  · simp
  · simp
  · rw [show (1 : ZMod 2) + 1 = 0 from rfl,parityValue_zero,parityValue_one]
    simp

def lastIndex (m : ℕ) [NeZero m] : Fin m := ⟨m-1,by have := NeZero.ne m; omega⟩

noncomputable def selectionCharacter (m : ℕ) [NeZero m] :
    Multiplicative (Fin m → ZMod 2) →* ℂˣ where
  toFun c := parityValue (c.toAdd (lastIndex m))
  map_one' := parityValue_zero
  map_mul' first second := parityValue_add (first.toAdd (lastIndex m))
    (second.toAdd (lastIndex m))

@[simp] theorem selectionCharacter_basis (m : ℕ) [NeZero m] (i : Fin m) :
    selectionCharacter m (Multiplicative.ofAdd (Pi.single i 1)) =
      if i = lastIndex m then -1 else 1 := by
  classical
  change parityValue ((Pi.single i (1 : ZMod 2) : Fin m → ZMod 2) (lastIndex m)) = _
  by_cases h : i = lastIndex m
  · subst i
    simp
  · simp [h,Ne.symm h]

end LittleFinitistic

end OAI
