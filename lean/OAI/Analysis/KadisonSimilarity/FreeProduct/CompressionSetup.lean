import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeCreationDischarge
import OAI.Analysis.KadisonSimilarity.FreeProduct.GeneratedWordDensity

namespace OAI

/-! The opposite head coordinates and the tail projection for compression. -/

noncomputable section
namespace KadisonSimilarity

section Projections
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def isometryRangeProjection (j : E →ₗᵢ[ℂ] F) : F →L[ℂ] F :=
  j.toContinuousLinearMap.comp j.toContinuousLinearMap.adjoint

theorem isometryRangeProjection_adjoint (j : E →ₗᵢ[ℂ] F) :
    (isometryRangeProjection j).adjoint = isometryRangeProjection j := by
  simp only [isometryRangeProjection, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

theorem isometryRangeProjection_sq (j : E →ₗᵢ[ℂ] F) :
    isometryRangeProjection j * isometryRangeProjection j = isometryRangeProjection j := by
  let J := j.toContinuousLinearMap
  have hj : J.adjoint.comp J = 1 := j.adjoint_comp_self
  change (J.comp J.adjoint).comp (J.comp J.adjoint) = J.comp J.adjoint
  rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc J.adjoint J,
    hj, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

theorem isometryRangeProjection_norm (j : E →ₗᵢ[ℂ] F) :
    ‖isometryRangeProjection j‖ ≤ 1 := by
  have hj : ‖j.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp only [LinearIsometry.coe_toContinuousLinearMap, j.norm_map, one_mul, le_refl]
  calc
    _ ≤ ‖j.toContinuousLinearMap‖ * ‖j.toContinuousLinearMap.adjoint‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖j.toContinuousLinearMap‖ * ‖j.toContinuousLinearMap‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ 1 * 1 := mul_le_mul hj hj (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem isometryRangeProjection_apply (j : E →ₗᵢ[ℂ] F) (x : E) :
    isometryRangeProjection j (j x) = j x := by
  change j (j.toContinuousLinearMap.adjoint (j x)) = j x
  have h := congrArg (fun f : E →L[ℂ] E => f x) j.adjoint_comp_self
  exact congrArg j h

theorem subtypeRangeProjection (S : ClosedSubmodule ℂ E) [CompleteSpace S.toSubmodule] :
    isometryRangeProjection S.toSubmodule.subtypeₗᵢ = S.toSubmodule.starProjection := by
  change S.toSubmodule.subtypeL.comp S.toSubmodule.subtypeL.adjoint = _
  rw [S.toSubmodule.adjoint_subtypeL]
  rfl

end Projections

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)

theorem reducedWordGenerated_swap (hτ : G.trace 1 = 1) (hgen : ReducedWordGenerated G A D) :
    ReducedWordGenerated G D A := by
  apply G.reducedWordGenerated_of_factorsTraciallyGenerate D A hτ
  have hg := G.factorsTraciallyGenerate_of_reducedWordGenerated A D hgen
  have he : TracialCornerGeometry.factorAlgebra D A = TracialCornerGeometry.factorAlgebra A D := by
    unfold TracialCornerGeometry.factorAlgebra
    rw [Set.union_comm]
  change DenseRange (G.vector.comp (TracialCornerGeometry.factorAlgebra D A).subtype.toLinearMap)
  rw [he]
  exact hg

end KadisonSimilarity

end

end OAI
