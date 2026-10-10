import OAI.Analysis.FiniteFactor.OrbitSampling.TrimmedWeak
import OAI.Analysis.FiniteFactor.OrbitSampling.TrimmedMarginals
import OAI.Analysis.FiniteFactor.OrbitSampling.OrbitSupport
import OAI.Analysis.FiniteFactor.OrbitSampling.LambdaMass
import OAI.Analysis.FiniteFactor.OrbitSampling.LambdaMarginals

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceOrderedSampling_event : ∀ᵐ θ ∂sourceAngleLaw,
    ∀ I : Finset SourceCoordinate,
      (∀ f : C(SourceSamplingTorus,ℝ),
        Tendsto (fun s => ∫ p, f p ∂(sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus))
          atTop (𝓝 (∫ p, f p ∂(sourceSamplingLambdaTorus I : Measure SourceSamplingTorus)))) ∧
      (∀ s, ∀ᵐ p ∂sourceSamplingTrimmed I s θ,
        (∀ i, p.1 i ≤ p.2 i) ∧ ∃ n ∈ sourceSamplingPowers s, 0 < n ∧ p.2 = coordinateRotate θ n p.1) ∧
      (∀ r : Bool, ∃ C : ℝ, ∀ s, ∃ g : (SourceCoordinate → ℝ) → ℝ,
        Measurable g ∧ (∀ x, 0 ≤ g x) ∧
        (sourceSamplingTrimmed I s θ).map (sourceSamplingEndpoint r) =
          sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal (g x)) ∧
        MemLp g 2 sourceSamplingHaar ∧ (∫ x, g x^2 ∂sourceSamplingHaar) ≤ C) ∧
      (∀ᶠ s in atTop, 0 < ((sourceSamplingTrimmed I s θ) Set.univ).toReal) := by
  filter_upwards [sourceSamplingTrimmed_weak_event,sourceSamplingTrimmed_marginals_event] with θ hw hm
  intro I
  refine ⟨(hw I).2.2,fun s => sourceSamplingTrimmed_orbits I s θ,hm I,?_⟩
  have hmass : Tendsto (fun s => ((sourceSamplingTrimmed I s θ) Set.univ).toReal) atTop
      (𝓝 (((sourceSamplingLambda I) Set.univ).toReal)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp (hw I).1.mass
  exact hmass.eventually (Ioi_mem_nhds (sourceSamplingLambda_mass_pos I))

end
end FiniteFactor

end OAI
