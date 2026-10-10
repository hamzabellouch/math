import OAI.Analysis.FiniteFactor.OrbitSampling.TorusMarginals
import OAI.Analysis.FiniteFactor.OrbitSampling.TorusSupport
import OAI.Analysis.FiniteFactor.CrossedProduct.OrderedSampling

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

structure SourceOrderedTorusSampling (θ : SourceCoordinate → ℝ) : Prop where
  weak : ∀ (I : Finset SourceCoordinate) (f : C(SourceSamplingTorus,ℝ)),
    Tendsto (fun s => ∫ p, f p ∂(sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus))
      atTop (𝓝 (∫ p, f p ∂(sourceSamplingLambdaTorus I : Measure SourceSamplingTorus)))
  support : ∀ (I : Finset SourceCoordinate) (s : ℕ),
    ∀ᵐ p ∂(sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus),
      (∀ i, sourceTorusRepresentative p.1 i ≤ sourceTorusRepresentative p.2 i) ∧
      ∃ n ∈ sourceSamplingPowers s, 0 < n ∧ p.2 = sourceTorusRotate θ n p.1
  marginals : ∀ (I : Finset SourceCoordinate) (r : Bool), ∃ C : ℝ, ∀ s,
    ∃ g : SourceTorus → ℝ, Measurable g ∧ (∀ z, 0 ≤ g z) ∧
      (sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus).map (sourceTorusEndpoint r) =
        sourceTorusHaar.withDensity (fun z => ENNReal.ofReal (g z)) ∧
      MemLp g 2 sourceTorusHaar ∧ (∫ z, g z^2 ∂sourceTorusHaar) ≤ C
  positive : ∀ I : Finset SourceCoordinate, ∀ᶠ s in atTop,
    0 < ((sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus) Set.univ).toReal

theorem sourceOrderedTorusSampling_event : ∀ᵐ θ ∂sourceAngleLaw, SourceOrderedTorusSampling θ := by
  filter_upwards [sourceOrderedSampling_event,sourceSamplingTrimmed_torus_marginals_event] with θ hs hm
  refine ⟨fun I => (hs I).1,fun I s => sourceSamplingTrimmed_torus_orbits I s θ,hm,?_⟩
  intro I
  have he (s : ℕ) : (sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus) Set.univ =
      sourceSamplingTrimmed I s θ Set.univ := by
    exact Measure.map_apply sourceSamplingTorusMap_continuous.measurable MeasurableSet.univ
  simpa only [he] using (hs I).2.2.2

end
end FiniteFactor

end OAI
