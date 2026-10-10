import OAI.Analysis.FiniteFactor.OrbitSampling.CylinderBasis
import OAI.Analysis.FiniteFactor.FiniteMeasureCylinderCriterion

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

def sourceSamplingUntrimmedFinite (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) : FiniteMeasure SourceSamplingPair :=
  ⟨sourceSamplingUntrimmed I s θ,inferInstance⟩

def sourceSamplingLambdaFinite (I : Finset SourceCoordinate) : FiniteMeasure SourceSamplingPair :=
  ⟨sourceSamplingLambda I,inferInstance⟩

theorem sourceSamplingCylinder_mass_eq {μ : Measure SourceSamplingPair}
    (hμ : ∀ᵐ p ∂μ, p ∈ sourceSamplingCube) (T : SourceSamplingRationalTest) :
    μ (sourceSamplingCylinder T) =
      μ (sourceSamplingRectangle (sourceSamplingRationalX T) (sourceSamplingRationalY T)) := by
  apply measure_congr
  filter_upwards [hμ] with p hp
  exact propext (sourceSamplingCylinder_on_cube T p hp)

/-- Actual finite measures converge weakly on the full real product. The
normalization and total-mass obligations are discharged by the empty test;
the original full sampling error is retained through the rectangle event. -/
theorem sourceSamplingUntrimmed_weak_event : ∀ᵐ θ ∂sourceAngleLaw,
    ∀ I : Finset SourceCoordinate,
      Tendsto (fun s => sourceSamplingUntrimmedFinite I s θ) atTop
        (𝓝 (sourceSamplingLambdaFinite I)) := by
  filter_upwards [sourceSamplingLambda_rectangle_limit_event,sourceSampling_mass_limit_event]
    with θ hrect hmass
  intro I
  apply finiteMeasure_tendsto_of_piSystem sourceSamplingCylinder_piSystem
  · rintro _ ⟨T,rfl⟩
    exact sourceSamplingCylinder_measurable T
  · exact sourceSamplingCylinder_basis
  · apply NNReal.tendsto_coe.mp
    exact hmass I
  · rintro _ ⟨T,rfl⟩
    apply NNReal.tendsto_coe.mp
    have h := hrect I T
    have hu (s : ℕ) := sourceSamplingCylinder_mass_eq (sourceSamplingUntrimmed_cube I s θ) T
    have hl := sourceSamplingCylinder_mass_eq (sourceSamplingLambda_cube I) T
    change Tendsto (fun s => ((sourceSamplingUntrimmed I s θ) (sourceSamplingCylinder T)).toReal)
      atTop (𝓝 (((sourceSamplingLambda I) (sourceSamplingCylinder T)).toReal))
    simpa only [← hu,← hl] using h

end
end FiniteFactor

end OAI
