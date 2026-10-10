import OAI.Analysis.Pureness.Comparison.SpatialIdentification
import OAI.Analysis.Pureness.Comparison.MatrixExtendedTrace
import OAI.Analysis.Pureness.Comparison.FiniteRootCompatibility

namespace OAI
noncomputable section
open scoped CStarAlgebra ComplexOrder ENNReal
namespace CuntzComparison
open CuntzTrace
variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : Function.Injective π)

instance : PartialOrder (SpatialStabilization π) := CStarAlgebra.spectralOrder _
instance : StarOrderedRing (SpatialStabilization π) := CStarAlgebra.spectralOrderedRing _

def spatialInverse : SpatialStabilization π →⋆ₙₐ[ℂ] MatrixLimit A :=
  (spatialEquiv π hπ).symm.toNonUnitalStarAlgHom

@[simp] lemma spatialInverse_stage (n : ℕ) (M : FinMatrix A n) :
    spatialInverse π hπ (spatialStage π n M) = matrixLimitStage n M :=
  (spatialEquiv π hπ).symm_apply_apply _

def TracialState.spatialTrace (τ : TracialState A) : ExtendedTrace (SpatialStabilization π) :=
  τ.matrixExtendedTrace.pullback (spatialInverse π hπ)

lemma spatialInverse_positive_stage (n : ℕ) (a : Positive (FinMatrix A n)) :
    Positive.map (spatialInverse π hπ) (Positive.map (spatialStage π n) a) =
      Positive.map (matrixLimitStage n) a := Subtype.ext (spatialInverse_stage π hπ n a.1)

@[simp] theorem TracialState.spatialTrace_stage (τ : TracialState A) (n : ℕ)
    (a : Positive (FinMatrix A n)) :
    τ.spatialTrace π hπ (Positive.map (spatialStage π n) a) =
      τ.extendedTrace.matrixTrace (Fin n) a := by
  change τ.matrixExtendedTrace (Positive.map (spatialInverse π hπ) (Positive.map (spatialStage π n) a)) = _
  rw [spatialInverse_positive_stage, τ.matrixExtendedTrace_stage]

theorem TracialState.spatialTrace_rank_stage (τ : TracialState A) (n : ℕ)
    (a : Positive (FinMatrix A n)) :
    (τ.spatialTrace π hπ).rank (Positive.map (spatialStage π n) a) =
      (τ.extendedTrace.matrixTrace (Fin n)).rank a := by
  rw [← ExtendedTrace.rank_pullback]
  have he : (τ.spatialTrace π hπ).pullback (spatialStage π n) = τ.extendedTrace.matrixTrace (Fin n) := by
    ext b
    exact τ.spatialTrace_stage π hπ n b
  rw [he]

theorem TracialState.spatialTrace_rank_eq_supportMass (τ : TracialState A) (n : ℕ) [NeZero n]
    (a : Positive (FinMatrix A n)) :
    (τ.spatialTrace π hπ).rank (Positive.map (spatialStage π n) a) = τ.matrixSupportMass a.1 a.2 := by
  rw [τ.spatialTrace_rank_stage π hπ, τ.extended_matrixRank]
end CuntzComparison

end

end OAI
