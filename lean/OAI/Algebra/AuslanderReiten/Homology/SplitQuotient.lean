import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace OAI

namespace ArExplicit

def eightCoordinates (k : Type*) [CommSemiring k] :
    (((k × k) × (k × k)) × ((k × k) × (k × k))) ≃ₐ[k] (Fin 8 → k) where
  toFun a := ![a.1.1.1, a.1.1.2, a.1.2.1, a.1.2.2, a.2.1.1, a.2.1.2, a.2.2.1, a.2.2.2]
  invFun a := (((a 0, a 1), (a 2, a 3)), ((a 4, a 5), (a 6, a 7)))
  left_inv a := rfl
  right_inv a := by ext i; fin_cases i <;> rfl
  map_mul' a b := by ext i; fin_cases i <;> rfl
  map_add' a b := by ext i; fin_cases i <;> rfl
  commutes' c := by ext i; fin_cases i <;> rfl

end ArExplicit

end OAI
