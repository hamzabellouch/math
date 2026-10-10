import OAI.Analysis.FiniteFactor.OrbitSampling.OrderedRestriction
import OAI.Analysis.FiniteFactor.SubmeasureL2Density

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

/-- Each actual trimmed marginal is dominated by the actual untrimmed
marginal, for both orientations. -/
theorem sourceSamplingTrimmed_marginal_le (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (r : Bool) :
    (sourceSamplingTrimmed I s θ).map (sourceSamplingEndpoint r) ≤
      (sourceSamplingUntrimmed I s θ).map (sourceSamplingEndpoint r) :=
  Measure.map_mono (sourceSamplingTrimmed_le I s θ) (sourceSamplingEndpoint_measurable r)

/-- The actual Radon--Nikodym densities after trimming have the same uniform
squared L2 bound, on a single event for every finite I and both endpoints. -/
theorem sourceSamplingTrimmed_marginals_event : ∀ᵐ θ ∂sourceAngleLaw,
    ∀ (I : Finset SourceCoordinate) (r : Bool), ∃ C : ℝ, ∀ s : ℕ,
      ∃ g : (SourceCoordinate → ℝ) → ℝ,
        Measurable g ∧ (∀ x, 0 ≤ g x) ∧
        (sourceSamplingTrimmed I s θ).map (sourceSamplingEndpoint r) =
          sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal (g x)) ∧
        MemLp g 2 sourceSamplingHaar ∧ (∫ x, g x^2 ∂sourceSamplingHaar) ≤ C := by
  filter_upwards [sourceSampling_both_marginals_event] with θ hθ
  intro I r
  obtain ⟨C,hC⟩ := hθ I r
  refine ⟨C,fun s => ?_⟩
  obtain ⟨f,hf,hLp,hbound⟩ := hC s
  have hsub := sourceSamplingTrimmed_marginal_le I s θ r
  rw [hf] at hsub
  obtain ⟨g,hg,hg0,hgμ,hle,hgLp,hgint⟩ := submeasure_L2_density sourceSamplingHaar
    ((sourceSamplingTrimmed I s θ).map (sourceSamplingEndpoint r)) f hLp hsub
  exact ⟨g,hg,hg0,hgμ,hgLp,hgint.trans hbound⟩

end
end FiniteFactor

end OAI
