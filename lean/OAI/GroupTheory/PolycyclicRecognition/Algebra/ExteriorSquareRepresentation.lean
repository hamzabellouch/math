import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExteriorSquarePairing
import Mathlib.RepresentationTheory.Basic

namespace OAI

/-! # The diagonal representation on the exterior square -/

noncomputable section
namespace PolycyclicRecognition
variable {Q M : Type} [Monoid Q] [AddCommGroup M]

def exteriorSquareRepresentation (ρ : Representation ℤ Q M) :
    Representation ℤ Q (⋀[ℤ]^2 M) where
  toFun q := exteriorPower.map 2 (ρ q)
  map_one' := by
    rw [map_one]
    exact exteriorPower.map_id
  map_mul' p q := by
    rw [map_mul]
    exact exteriorPower.map_comp (ρ q) (ρ p)

@[simp] theorem exteriorSquareRepresentation_value (ρ : Representation ℤ Q M)
    (q : Q) (x y : M) :
    exteriorSquareRepresentation ρ q (exteriorSquareValue x y) =
      exteriorSquareValue (ρ q x) (ρ q y) := by
  change exteriorPower.map 2 (ρ q) (exteriorPower.ιMulti ℤ 2 ![x, y]) = _
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

end PolycyclicRecognition

end

end OAI
