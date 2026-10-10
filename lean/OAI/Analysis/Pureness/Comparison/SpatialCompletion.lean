import OAI.Analysis.Pureness.Comparison.SpatialFiniteMatrices
import OAI.Analysis.Pureness.Stabilization.MatrixLimitLift

namespace OAI
noncomputable section
open scoped CStarAlgebra Topology
namespace CuntzComparison
open CuntzTrace
variable {A H : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))

instance stabilizationOperatorsCStar : CStarAlgebra (StabilizationOperators H) :=
  inferInstanceAs (CStarAlgebra (SpatialHilbert H StandardHilbert →L[ℂ] SpatialHilbert H StandardHilbert))
instance stabilizationOperatorsContinuousStar : ContinuousStar (StabilizationOperators H) :=
  inferInstanceAs (ContinuousStar (SpatialHilbert H StandardHilbert →L[ℂ] SpatialHilbert H StandardHilbert))
instance stabilizationOperatorsTopologicalRing : IsTopologicalRing (StabilizationOperators H) :=
  inferInstanceAs (IsTopologicalRing (SpatialHilbert H StandardHilbert →L[ℂ] SpatialHilbert H StandardHilbert))

def spatialRepresentation : MatrixLimit A →⋆ₙₐ[ℂ] StabilizationOperators H :=
  matrixLimitLift (A := A) (B := StabilizationOperators H) (spatialFinite π) (spatialFinite_compatible π)

@[simp] theorem spatialRepresentation_stage (n : ℕ) (M : FinMatrix A n) :
    spatialRepresentation π (matrixLimitStage n M) = spatialFinite π n M :=
  matrixLimitLift_stage _ _ n M

lemma spatialRepresentation_continuous : Continuous (spatialRepresentation π) := by
  have h : LipschitzWith 1 (spatialRepresentation π) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul] using
      NonUnitalStarAlgHom.norm_apply_le (spatialRepresentation π) (x-y)
  exact h.continuous

theorem spatialRepresentation_norm (hπ : Function.Injective π) (x : MatrixLimit A) :
    ‖spatialRepresentation π x‖ = ‖x‖ := by
  refine finiteMatrixSubalgebra_dense.induction_on x ?_ ?_
  · have hc : Continuous (fun x : MatrixLimit A => ‖spatialRepresentation π x‖) :=
      continuous_norm.comp (spatialRepresentation_continuous π)
    exact isClosed_eq hc continuous_norm
  · intro y
    obtain ⟨n,M,rfl⟩ := finiteMatrixStage_surjective y
    change ‖spatialRepresentation π (matrixLimitStage n M)‖ = ‖matrixLimitStage n M‖
    rw [spatialRepresentation_stage, matrixLimitStage_norm]
    exact NonUnitalStarAlgHom.norm_map _ (spatialFinite_injective π hπ n) M

theorem spatialRepresentation_isometry (hπ : Function.Injective π) :
    Isometry (spatialRepresentation π) :=
  AddMonoidHomClass.isometry_of_norm (spatialRepresentation π) (spatialRepresentation_norm π hπ)

def spatialMatrixAlgebra : NonUnitalStarSubalgebra ℂ (StabilizationOperators H) :=
  (NonUnitalStarAlgebra.adjoin ℂ {T | ∃ (n : ℕ) (M : FinMatrix A n), T = spatialFinite π n M}).topologicalClosure

lemma spatialRepresentation_mem (x : MatrixLimit A) :
    spatialRepresentation π x ∈ spatialMatrixAlgebra π := by
  refine finiteMatrixSubalgebra_dense.induction_on x ?_ ?_
  · exact (NonUnitalStarSubalgebra.isClosed_topologicalClosure _).preimage
      (spatialRepresentation_continuous π)
  · intro y
    obtain ⟨n,M,rfl⟩ := finiteMatrixStage_surjective y
    change spatialRepresentation π (matrixLimitStage n M) ∈ _
    rw [spatialRepresentation_stage]
    exact NonUnitalStarSubalgebra.le_topologicalClosure _
      (NonUnitalStarAlgebra.subset_adjoin ℂ _ ⟨n,M,rfl⟩)

theorem spatialRepresentation_range (hπ : Function.Injective π) :
    Set.range (spatialRepresentation π) = (spatialMatrixAlgebra π : Set (StabilizationOperators H)) := by
  apply Set.Subset.antisymm
  · rintro T ⟨x,rfl⟩; exact spatialRepresentation_mem π x
  · have hr : IsClosed (Set.range (spatialRepresentation π)) :=
      (spatialRepresentation_isometry π hπ).isClosedEmbedding.isClosed_range
    apply closure_minimal ?_ hr
    intro T hT
    induction hT using NonUnitalStarAlgebra.adjoin_induction with
    | mem T hT =>
      obtain ⟨n,M,rfl⟩ := hT
      exact ⟨matrixLimitStage n M, spatialRepresentation_stage π n M⟩
    | zero => exact ⟨0,map_zero _⟩
    | add T S _ _ hT hS =>
      obtain ⟨x,rfl⟩ := hT; obtain ⟨y,rfl⟩ := hS
      exact ⟨x+y,map_add _ _ _⟩
    | mul T S _ _ hT hS =>
      obtain ⟨x,rfl⟩ := hT; obtain ⟨y,rfl⟩ := hS
      exact ⟨x*y,map_mul _ _ _⟩
    | smul c T _ hT =>
      obtain ⟨x,rfl⟩ := hT; exact ⟨c • x,map_smul _ _ _⟩
    | star T _ hT =>
      obtain ⟨x,rfl⟩ := hT; exact ⟨star x,map_star _ _⟩
end CuntzComparison

end

end OAI
