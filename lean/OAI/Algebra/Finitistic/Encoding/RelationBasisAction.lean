import OAI.Algebra.Finitistic.Encoding.RelationBasisCoefficients
import OAI.Algebra.Finitistic.Selection.SelectionEncoding

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.RelationBasisAction
open QuadraticEncoding RelationBasisCoefficients
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {d t : ℕ} (P : Relations k d t) (x : Fin d → R)

/-- The distinguished arrow acts by one, followed by the original generators. -/
def arrow : Fin (d+1) → R := Fin.cases 1 x

/-- Evaluate a length-two path b a in the original algebra. -/
def pathValue : Paths k d →ₗ[k] R :=
  (pathBasis (k := k) (d := d)).constr k (fun ba => arrow x ba.1 * arrow x ba.2)

@[simp] theorem pathValue_basis (b a : Fin (d+1)) :
    pathValue x (basis b ⊗ₜ[k] basis a) = arrow x b * arrow x a := by
  have hb : (pathBasis (k := k) (d := d)) (b,a) = basis b ⊗ₜ[k] basis a := by
    simp [pathBasis,basis]
  rw [← hb]
  exact (pathBasis (k := k) (d := d)).constr_basis k _ (b,a)

variable (hx : ∀ j, (∑ h, ∑ l, P.quadratic j h l • (x h * x l)) +
  (∑ h, P.linear j h • x h) + P.constant j • (1 : R) = 0)

include hx in
/-- The entire relation space vanishes, including every chosen independent basis vector. -/
theorem relationSpace_le_kernel : relationSpace P ≤ (pathValue x).ker := by
  apply Submodule.span_le.2
  rintro z (⟨h,rfl⟩ | ⟨j,rfl⟩)
  · change pathValue x (commutation h) = 0
    simp [commutation,arrow]
  · change pathValue x (homogenized P j) = 0
    simpa only [homogenized,map_add,map_sum,map_smul,pathValue_basis,arrow,
      Fin.cases_zero,Fin.cases_succ,one_mul,mul_one] using hx j

include hx in
/-- Exact homogeneous coefficient equations for the fixed-diagram lifting theorem. -/
theorem basis_action_relation (r : RelationIndex P) :
    (∑ a, ∑ b, basisCoefficient P r a b • (arrow x b * arrow x a)) = 0 := by
  have hz := relationSpace_le_kernel P x hx (RelationSequence.relationBasis P r).property
  change pathValue x (RelationSequence.relationBasis P r).val = 0 at hz
  rw [← expansion P (RelationSequence.relationBasis P r)] at hz
  simpa only [map_sum,map_smul,pathValue_basis,basisCoefficient] using hz

/-- The concrete selected algebra satisfies all equations of the independent relation basis. -/
theorem encoding_basis_action (E : SelectionEncoding.Encoding k R) (r : RelationIndex E.relations) :
    (∑ a, ∑ b, basisCoefficient E.relations r a b •
      (arrow (SelectionEncoding.generator E) b * arrow (SelectionEncoding.generator E) a)) = 0 :=
  basis_action_relation E.relations (SelectionEncoding.generator E)
    (SelectionEncoding.generator_relations E) r
end LittleFinitistic.RelationBasisAction

end

end OAI
