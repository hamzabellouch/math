import OAI.Analysis.KadisonSimilarity.FreeProduct.CompressionSetup

namespace OAI

/-! Orthogonal inclusion projections in the head tensor coordinates. -/

noncomputable section
namespace KadisonSimilarity

variable {E F K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem isometryRangeProjection_comp (j : E →ₗᵢ[ℂ] F) (u : F →ₗᵢ[ℂ] K) :
    isometryRangeProjection (u.comp j) = u.toContinuousLinearMap.comp
      ((isometryRangeProjection j).comp u.toContinuousLinearMap.adjoint) := by
  change (u.toContinuousLinearMap.comp j.toContinuousLinearMap).comp
    (u.toContinuousLinearMap.comp j.toContinuousLinearMap).adjoint = _
  simp only [ContinuousLinearMap.adjoint_comp, isometryRangeProjection,
    ContinuousLinearMap.comp_assoc]

theorem isometryRangeProjection_complement (u : E ≃ₗᵢ[ℂ] F)
    (S T : ClosedSubmodule ℂ E) [CompleteSpace S.toSubmodule] [CompleteSpace T.toSubmodule]
    (hST : S.toSubmoduleᗮ = T.toSubmodule) :
    isometryRangeProjection (u.toLinearIsometry.comp S.toSubmodule.subtypeₗᵢ) =
      1 - isometryRangeProjection (u.toLinearIsometry.comp T.toSubmodule.subtypeₗᵢ) := by
  have hp : S.toSubmodule.starProjection = 1 - T.toSubmodule.starProjection := by
    have ht : T.toSubmodule.starProjection = 1 - S.toSubmodule.starProjection := by
      simpa only [hST] using (Submodule.starProjection_orthogonal' S.toSubmodule)
    rw [ht]
    abel
  rw [isometryRangeProjection_comp, isometryRangeProjection_comp,
    subtypeRangeProjection, subtypeRangeProjection, hp]
  have huadj : u.toLinearIsometry.toContinuousLinearMap.adjoint =
      u.symm.toLinearIsometry.toContinuousLinearMap := u.adjoint_eq_symm
  simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, huadj]
  have hu : u.toLinearIsometry.toContinuousLinearMap.comp
      u.symm.toLinearIsometry.toContinuousLinearMap = 1 := by
    ext x
    exact u.apply_symm_apply x
  rw [hu, ContinuousLinearMap.one_def]

omit [CompleteSpace E] in
/-- Factoring the inclusion through the vacuum insertion gives the exact
first-letter projection used in the compression model. -/
theorem firstLetterProjection_of_inclusion
    (Ω : E) (j : F →ₗᵢ[ℂ] K) (v : F →ₗᵢ[ℂ] HilbertTensor E K)
    (hv : v.toContinuousLinearMap = (hilbertTensorInsert Ω).comp j.toContinuousLinearMap) :
    firstLetterProjection Ω (isometryRangeProjection j) = isometryRangeProjection v := by
  simp only [isometryRangeProjection]
  rw [hv, ContinuousLinearMap.adjoint_comp]
  simp only [firstLetterProjection, ContinuousLinearMap.comp_assoc]

end KadisonSimilarity

end

end OAI
