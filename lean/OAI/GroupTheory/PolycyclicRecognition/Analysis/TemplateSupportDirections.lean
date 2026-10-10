import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWordModel

namespace OAI

/-! # Exponents of a finite family of actual support positions -/

namespace PolycyclicRecognition.CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

/-- Each generator uses its own prescribed supporting Cartan position. -/
def templateSupportExponent (v : Fin M.letterCount → H) (i : Fin M.letterCount) : ℝ :=
  M.weight i (v i)

end PolycyclicRecognition.CartanWordModel

end OAI
