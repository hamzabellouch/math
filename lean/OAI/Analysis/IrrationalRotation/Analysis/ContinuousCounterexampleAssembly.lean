import OAI.Analysis.IrrationalRotation.Model.ParameterCircleOperator
import OAI.Analysis.IrrationalRotation.Operators.ContinuousProjectionTransport
import OAI.Analysis.IrrationalRotation.Spectral.RotationDeterminant
import OAI.Analysis.IrrationalRotation.Rotation.RotationAlgebra
import OAI.Analysis.IrrationalRotation.Rotation.CircleBackgroundBumps

namespace OAI

/-! Continuous weights with the invariant-projection obstruction and their spectral properties. -/

noncomputable section
namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)

theorem continuousWeight_obstruction_of_measurableOperator
    (d : BackgroundBumpData θ)
    (hstar : HasOnlyTrivialInvariantProjections (Rotation.algebra θ)
      (p.measurableOperator θ hp)) :
    HasOnlyTrivialInvariantProjections (Rotation.algebra θ)
      (Rotation.weightedReal θ
        ⟨p.continuousWeight θ d, (hp.isContinuousCircleWeight_continuousWeight d).1⟩) := by
  apply hp.continuousWeight_hasOnlyTrivialInvariantProjections d
  exact hstar

theorem exists_continuous_invariant_weight
    (hθ : Irrational θ)
    (hstar : HasOnlyTrivialInvariantProjections (Rotation.algebra θ)
      (p.measurableOperator θ hp)) :
    ∃ f : C(Circle, ℝ), IsContinuousCircleWeight f ∧
      Rotation.weightedReal θ f ∈ Rotation.algebra θ ∧
      HasOnlyTrivialInvariantProjections (Rotation.algebra θ) (Rotation.weightedReal θ f) := by
  obtain ⟨d⟩ := BackgroundCost.exists_backgroundBumpData θ hθ
  let f : C(Circle, ℝ) :=
    ⟨p.continuousWeight θ d, (hp.isContinuousCircleWeight_continuousWeight d).1⟩
  have hf : IsContinuousCircleWeight f := hp.isContinuousCircleWeight_continuousWeight d
  exact ⟨f, hf, Rotation.weightedReal_mem_algebra θ f,
    hp.continuousWeight_obstruction_of_measurableOperator d hstar⟩

theorem exists_continuous_counterexample_of_measurable_obstruction
    (hθ : Irrational θ)
    (hstar : HasOnlyTrivialInvariantProjections (Rotation.algebra θ)
      (p.measurableOperator θ hp)) :
    ∃ f : C(Circle, ℝ), IsContinuousCircleWeight f ∧
      Rotation.weightedReal θ f ∈ Rotation.algebra θ ∧
      HasOnlyTrivialInvariantProjections (Rotation.algebra θ) (Rotation.weightedReal θ f) ∧
      Rotation.weightedReal θ f ≠ 0 ∧ NormQuasinilpotent (Rotation.weightedReal θ f) ∧
      vectorFugledeKadisonDeterminant Rotation.vacuum (Rotation.weightedReal θ f) = 0 := by
  obtain ⟨f, hf, hmem, hinv⟩ := hp.exists_continuous_invariant_weight hθ hstar
  exact ⟨f, hf, hmem, hinv, Rotation.continuous_weight_spectral_bundle θ hθ f hf⟩

end Invariant233.CircleParameterLaws

end

end OAI
