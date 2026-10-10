import OAI.Analysis.FiniteFactor.CrossedProduct.NormalFunctionalSpace

namespace OAI

namespace FiniteFactor
noncomputable section

def sourceVectorInSpace (θ : SourceCoordinate → ℝ) (ξ η : SourceHilbert SourceCoordinate) :
    SourceNormalPredualSpace θ := ⟨sourceVectorFunctional θ ξ η,sourceVectorFunctional_mem θ ξ η⟩

theorem sourceVectorInSpace_add_left (θ : SourceCoordinate → ℝ) (ξ ξ' η : SourceHilbert SourceCoordinate) :
    sourceVectorInSpace θ (ξ+ξ') η = sourceVectorInSpace θ ξ η + sourceVectorInSpace θ ξ' η := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro A
  change inner ℂ (ξ+ξ') (A.val η) = inner ℂ ξ (A.val η) + inner ℂ ξ' (A.val η)
  exact inner_add_left _ _ _

theorem sourceVectorInSpace_smul_left (θ : SourceCoordinate → ℝ) (c : ℂ) (ξ η : SourceHilbert SourceCoordinate) :
    sourceVectorInSpace θ (c • ξ) η = star c • sourceVectorInSpace θ ξ η := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro A
  change inner ℂ (c • ξ) (A.val η) = star c * inner ℂ ξ (A.val η)
  exact inner_smul_left _ _ _

theorem sourceVectorInSpace_add_right (θ : SourceCoordinate → ℝ) (ξ η η' : SourceHilbert SourceCoordinate) :
    sourceVectorInSpace θ ξ (η+η') = sourceVectorInSpace θ ξ η + sourceVectorInSpace θ ξ η' := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro A
  change inner ℂ ξ ((A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (η+η')) = inner ℂ ξ (A.val η) + inner ℂ ξ (A.val η')
  rw [map_add,inner_add_right]

theorem sourceVectorInSpace_smul_right (θ : SourceCoordinate → ℝ) (c : ℂ) (ξ η : SourceHilbert SourceCoordinate) :
    sourceVectorInSpace θ ξ (c • η) = c • sourceVectorInSpace θ ξ η := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro A
  change inner ℂ ξ ((A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (c • η)) = c * inner ℂ ξ (A.val η)
  rw [map_smul,inner_smul_right]

end
end FiniteFactor

end OAI
