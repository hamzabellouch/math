import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeProductMatrixExtension
import Mathlib.Algebra.Star.UnitaryStarAlgAut

namespace OAI

/-! Matrix conjugation as an actual star-algebra automorphism of the factor. -/

noncomputable section
namespace KadisonSimilarity.TracialCornerGeometry

variable {P : Type*} [CStarAlgebra P] (D : StarSubalgebra ℂ P)
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)

def matrixConjugationAut : D ≃⋆ₐ[ℂ] D :=
  Unitary.conjStarAlgAut ℂ D ⟨ι (u : Matrix α α ℂ), Unitary.map_mem ι u.property⟩

@[simp] theorem matrixConjugationAut_apply (d : D) :
    matrixConjugationAut D ι u d = matrixConjugateLetter D ι u d := rfl

@[simp] theorem matrixConjugateLetter_one_letter :
    matrixConjugateLetter D ι u 1 = 1 :=
  map_one (matrixConjugationAut D ι u)

@[simp] theorem matrixConjugateLetter_product (a b : D) :
    matrixConjugateLetter D ι u (a * b) =
      matrixConjugateLetter D ι u a * matrixConjugateLetter D ι u b :=
  map_mul (matrixConjugationAut D ι u) a b

@[simp] theorem matrixConjugateLetter_sub (a b : D) :
    matrixConjugateLetter D ι u (a - b) =
      matrixConjugateLetter D ι u a - matrixConjugateLetter D ι u b :=
  map_sub (matrixConjugationAut D ι u) a b

@[simp] theorem matrixConjugateLetter_smul (r : ℂ) (a : D) :
    matrixConjugateLetter D ι u (r • a) = r • matrixConjugateLetter D ι u a :=
  map_smul (matrixConjugationAut D ι u) r a

end KadisonSimilarity.TracialCornerGeometry

end

end OAI
