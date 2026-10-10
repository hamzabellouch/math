import OAI.Analysis.IrrationalRotation.Rotation.CircleParameterRecursion
import OAI.Analysis.IrrationalRotation.Sampling.CircleSamplingStageSupply

namespace OAI

namespace Invariant233

theorem exists_circle_parameters {θ : ℝ} (hθ : Irrational θ) :
    ∃ p : CircleParameterData, CircleParameterLaws θ p :=
  CircleParameterRecursion.exists_parameters_of_stage_supply hθ
    (circleSamplingStage_supply hθ)

end Invariant233

end OAI
