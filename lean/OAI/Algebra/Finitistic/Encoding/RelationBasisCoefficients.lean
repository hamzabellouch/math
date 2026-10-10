import OAI.Algebra.Finitistic.Encoding.RelationSequence

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.RelationBasisCoefficients
open QuadraticEncoding
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)

/-- The actual ordered length-two path basis, with the later arrow first. -/
def pathBasis : Module.Basis (Fin (d+1) × Fin (d+1)) k (Paths k d) :=
  (Pi.basisFun k (Fin (d+1))).tensorProduct (Pi.basisFun k (Fin (d+1)))

/-- Coefficient of the path b a in a vector of the actual relation subspace. -/
def coefficient (r : relationSpace P) (a b : Fin (d+1)) : k :=
  (pathBasis (k := k) (d := d)).repr r.val (b,a)

theorem expansion (r : relationSpace P) :
    (∑ a, ∑ b, coefficient P r a b • (basis b ⊗ₜ[k] basis a)) = r.val := by
  rw [Finset.sum_comm]
  simpa only [coefficient,pathBasis,Fintype.sum_prod_type,
    Module.Basis.tensorProduct_apply,Pi.basisFun_apply,basis] using
    (pathBasis (k := k) (d := d)).sum_repr r.val

/-- Every vector in the chosen relation basis gives the genuine algebra equation. -/
theorem algebra_relation (r : relationSpace P) :
    (∑ a, ∑ b, coefficient P r a b • (arrow12 P b * arrow01 P a)) = 0 := by
  have h := (pathMap_eq_zero_iff P r.val).2 r.property
  rw [← expansion P r] at h
  simpa only [map_sum,map_smul,← arrow_product] using h

abbrev RelationIndex := Fin (Module.finrank k (relationSpace P))

def basisCoefficient (r : RelationIndex P) (a b : Fin (d+1)) : k :=
  coefficient P (RelationSequence.relationBasis P r) a b

theorem basis_relation (r : RelationIndex P) :
    (∑ a, ∑ b, basisCoefficient P r a b • (arrow12 P b * arrow01 P a)) = 0 :=
  algebra_relation P (RelationSequence.relationBasis P r)
end LittleFinitistic.RelationBasisCoefficients

end

end OAI
