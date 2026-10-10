import OAI.Analysis.FiniteFactor.OrbitSampling.Cube
import OAI.Analysis.FiniteFactor.SubmeasureL2Density

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

def sourceSamplingLimitCoordinate (I : Finset SourceCoordinate) (r : Bool)
    (i : SourceCoordinate) (z : ℝ × ℝ) : ℝ := if r = true ∧ i ∈ I then z.2 else z.1

theorem sourceSamplingLimitCoordinate_preserving (I : Finset SourceCoordinate) (r : Bool)
    (i : SourceCoordinate) : MeasurePreserving (sourceSamplingLimitCoordinate I r i)
      (unitIntervalMeasure.prod unitIntervalMeasure) unitIntervalMeasure := by
  by_cases h : r = true ∧ i ∈ I
  · have he : sourceSamplingLimitCoordinate I r i = Prod.snd := by funext z; simp [sourceSamplingLimitCoordinate,h]
    rw [he]
    exact measurePreserving_snd
  · have he : sourceSamplingLimitCoordinate I r i = Prod.fst := by funext z; simp [sourceSamplingLimitCoordinate,h]
    rw [he]
    exact measurePreserving_fst

theorem sourceSamplingLimitEndpoint_eq (I : Finset SourceCoordinate) (r : Bool) :
    sourceSamplingEndpoint r ∘ sourceSamplingLimitMap I =
      (fun p i => sourceSamplingLimitCoordinate I r i (p i)) := by
  funext p i
  cases r <;> simp [sourceSamplingEndpoint,sourceSamplingLimitMap,sourceSamplingLimitCoordinate]

/-- Before the triangular restriction, either selected endpoint is exactly
product Haar, including the mixed first/second selection in the second endpoint. -/
theorem sourceSamplingLimitEndpoint_preserving (I : Finset SourceCoordinate) (r : Bool) :
    MeasurePreserving (sourceSamplingEndpoint r ∘ sourceSamplingLimitMap I)
      sourceSamplingPairHaar sourceSamplingHaar := by
  rw [sourceSamplingLimitEndpoint_eq]
  refine ⟨Measurable.of_eval (fun i => (sourceSamplingLimitCoordinate_preserving I r i).measurable.comp
    (measurable_pi_apply i)),?_⟩
  rw [Measure.infinitePi_map_pi _ (fun i => (sourceSamplingLimitCoordinate_preserving I r i).measurable)]
  simp only [(sourceSamplingLimitCoordinate_preserving I r _).map_eq]

/-- Both actual limiting marginals are submeasures of Haar. This proves the
absolute continuity needed for the later Lusin transfer without assuming a marginal law. -/
theorem sourceSamplingLambda_marginal_le (I : Finset SourceCoordinate) (r : Bool) :
    (sourceSamplingLambda I).map (sourceSamplingEndpoint r) ≤ sourceSamplingHaar := by
  rw [sourceSamplingLambda,Measure.map_map (sourceSamplingEndpoint_measurable r)
    (sourceSamplingLimitMap_measurable I)]
  have h := Measure.map_mono (μ := sourceSamplingPairHaar.restrict (sourceSamplingTriangleSet I))
    (ν := sourceSamplingPairHaar) Measure.restrict_le_self (sourceSamplingLimitEndpoint_preserving I r).measurable
  rwa [(sourceSamplingLimitEndpoint_preserving I r).map_eq] at h

theorem sourceSamplingLambda_marginal_density (I : Finset SourceCoordinate) (r : Bool) :
    ∃ g : (SourceCoordinate → ℝ) → ℝ,
      Measurable g ∧ (∀ x, 0 ≤ g x) ∧
      (sourceSamplingLambda I).map (sourceSamplingEndpoint r) =
        sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal (g x)) ∧
      (∀ᵐ x ∂sourceSamplingHaar, g x ≤ 1) ∧ MemLp g 2 sourceSamplingHaar ∧
      (∫ x, g x^2 ∂sourceSamplingHaar) ≤ 1 := by
  have h := sourceSamplingLambda_marginal_le I r
  have h' : (sourceSamplingLambda I).map (sourceSamplingEndpoint r) ≤
      sourceSamplingHaar.withDensity (fun _ => ENNReal.ofReal (1 : ℝ)) := by simpa using h
  obtain ⟨g,hg,hg0,hgm,hgle,hglp,hgint⟩ := submeasure_L2_density sourceSamplingHaar
    ((sourceSamplingLambda I).map (sourceSamplingEndpoint r)) (fun _ => 1) (memLp_const (1 : ℝ)) h'
  exact ⟨g,hg,hg0,hgm,by simpa using hgle,hglp,by simpa using hgint⟩

end
end FiniteFactor

end OAI
