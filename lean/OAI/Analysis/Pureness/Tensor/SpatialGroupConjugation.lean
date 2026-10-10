import OAI.Analysis.Pureness.Tensor.SpatialCoordinateProjection
import OAI.Analysis.Pureness.Tensor.SpatialGroupPolynomialMap
import OAI.Analysis.Pureness.Operators.UnitaryAverages

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct
variable {A H G : Type*} [Group G] [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H))

def spatialGroupRightHom : reducedGroupAlgebra G →⋆ₐ[ℂ]
    representedSpatialTensor α (reducedGroupAlgebra G).subtype := by
  let ι : reducedGroupAlgebra G →⋆ₐ[ℂ] A ⊗[ℂ] reducedGroupAlgebra G :=
    { Algebra.TensorProduct.includeRight with
      map_star' := by intro b; change (1 ⊗ₜ[ℂ] star b) = star (1 ⊗ₜ[ℂ] b); simp }
  exact (spatialCompletionMap α (reducedGroupAlgebra G).subtype).comp ι

def spatialGroupUnitary (g : G) : unitary (representedSpatialTensor α (reducedGroupAlgebra G).subtype) :=
  Unitary.map (StarMonoidHom.ofClass (spatialGroupRightHom (G := G) α)) (reducedGroupUnitary G g)

lemma spatialGroupUnitary_val (g : G) :
    ((spatialGroupUnitary α g : representedSpatialTensor α (reducedGroupAlgebra G).subtype) :
      SpatialHilbert H (GroupL2 G) →L[ℂ] SpatialHilbert H (GroupL2 G)) =
      spatialRightOperator (H := H) (groupLeft g) := by
  change spatialStarTensorHom α (reducedGroupAlgebra G).subtype
    (1 ⊗ₜ[ℂ] (reducedGroupUnitary G g : reducedGroupAlgebra G)) = _
  rw [spatialStarTensorHom_tmul, map_one]
  rfl

lemma spatialGroupUnitary_commute_left (g : G) (a : A) :
    Commute (spatialGroupUnitary α g : representedSpatialTensor α (reducedGroupAlgebra G).subtype)
      (spatialCompletionMap α (reducedGroupAlgebra G).subtype (a ⊗ₜ[ℂ] 1)) := by
  exact ((Commute.one_left a).tmul (Commute.one_right
    (reducedGroupUnitary G g : reducedGroupAlgebra G))).map
      (spatialCompletionMap α (reducedGroupAlgebra G).subtype)

lemma spatialGroupAverage_fixed_left {n : ℕ} (hn : n ≠ 0) (k : Fin n → G) (a : A) :
    unitaryAverage (B := representedSpatialTensor α (reducedGroupAlgebra G).subtype) (fun i => spatialGroupUnitary α (k i))
      (spatialCompletionMap α (reducedGroupAlgebra G).subtype (a ⊗ₜ[ℂ] 1)) =
      spatialCompletionMap α (reducedGroupAlgebra G).subtype (a ⊗ₜ[ℂ] 1) :=
  unitaryAverage_fixed (B := representedSpatialTensor α (reducedGroupAlgebra G).subtype) hn _ _ (fun i => spatialGroupUnitary_commute_left α (k i) a)
end CuntzPureness

end

end OAI
