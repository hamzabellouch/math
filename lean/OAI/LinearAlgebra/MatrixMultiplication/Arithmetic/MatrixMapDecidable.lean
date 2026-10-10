import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.FiniteFamily

namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

namespace MatrixMultiplication.AllFieldFiniteFamily

open MatrixMultiplication.Foundation

variable {F : Type*} [Field F]

private theorem matrixCoefficients_decidable (A B C : Type)
    (dA eA : DecidableEq A) (dB eB : DecidableEq B) (dC eC : DecidableEq C) :
    @Tensor.matrixCoefficients F _ A B C dA dB dC =
      @Tensor.matrixCoefficients F _ A B C eA eB eC := by
  have hA : dA = eA := Subsingleton.elim _ _
  have hB : dB = eB := Subsingleton.elim _ _
  have hC : dC = eC := Subsingleton.elim _ _
  cases hA
  cases hB
  cases hC
  rfl

namespace LocalMap

def redecideMatrix {X Y Z A B C : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    {source : Tensor F X Y Z}
    {dA : DecidableEq A} {dB : DecidableEq B} {dC : DecidableEq C}
    (map : LocalMap source (@Tensor.matrixCoefficients F _ A B C dA dB dC))
    (eA : DecidableEq A) (eB : DecidableEq B) (eC : DecidableEq C) :
    LocalMap source (@Tensor.matrixCoefficients F _ A B C eA eB eC) where
  x := map.x
  y := map.y
  z := map.z
  coefficient := map.coefficient.trans
    (matrixCoefficients_decidable A B C dA eA dB eB dC eC)

end LocalMap
end MatrixMultiplication.AllFieldFiniteFamily

end

end OAI
