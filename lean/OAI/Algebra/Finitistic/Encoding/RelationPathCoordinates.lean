import OAI.Algebra.Finitistic.Encoding.PathBasisIso

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.RelationPathCoordinates
open QuadraticEncoding RelationBasisCoefficients
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

abbrev coordinates : Paths k d ≃ₗ[k] (Fin (d+1) → Arrows k d) :=
  TensorProduct.piScalarRight k k (Arrows k d) (Fin (d+1))

/-- The coefficient matrix of an actual relation, grouped by its first traversed arrow. -/
theorem relation_coordinate (r : relationSpace P) (a : Fin (d+1)) :
    coordinates (r : Paths k d) a = ∑ b, coefficient P r a b • basis b := by
  have h := congrArg (fun z : Paths k d => coordinates z a) (expansion P r)
  simpa [coordinates,TensorProduct.piScalarRightHom_tmul,Finset.sum_apply,
    basis,Pi.single_apply] using h.symm

/-- The actual independent relation basis has precisely the manuscript's q coefficients. -/
theorem basis_coordinate (r : RelationIndex P) (a : Fin (d+1)) :
    coordinates ((RelationSequence.relationBasis P r : relationSpace P) : Paths k d) a =
      ∑ b, basisCoefficient P r a b • basis b :=
  relation_coordinate P (RelationSequence.relationBasis P r) a
end LittleFinitistic.RelationPathCoordinates

end

end OAI
