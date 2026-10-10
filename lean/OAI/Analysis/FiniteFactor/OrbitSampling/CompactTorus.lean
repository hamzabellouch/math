import OAI.Analysis.FiniteFactor.OrbitSampling.WeakLimit
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Instances.AddCircle.Real

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

abbrev SourceSamplingTorus := (SourceCoordinate → UnitAddCircle) × (SourceCoordinate → UnitAddCircle)

instance sourceSamplingTorus_compact : CompactSpace SourceSamplingTorus := inferInstance

instance sourceSamplingTorus_borel : BorelSpace SourceSamplingTorus := Prod.borelSpace

def sourceSamplingTorusMap (p : SourceSamplingPair) : SourceSamplingTorus :=
  (fun i => (p.1 i : UnitAddCircle),fun i => (p.2 i : UnitAddCircle))

theorem sourceSamplingTorusMap_continuous : Continuous sourceSamplingTorusMap := by
  exact (continuous_pi (fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp
    ((continuous_apply i).comp continuous_fst))).prodMk
    (continuous_pi (fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((continuous_apply i).comp continuous_snd)))

def sourceSamplingUntrimmedTorus (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) : FiniteMeasure SourceSamplingTorus :=
  (sourceSamplingUntrimmedFinite I s θ).map sourceSamplingTorusMap

def sourceSamplingLambdaTorus (I : Finset SourceCoordinate) : FiniteMeasure SourceSamplingTorus :=
  (sourceSamplingLambdaFinite I).map sourceSamplingTorusMap

theorem sourceSamplingUntrimmed_torus_event : ∀ᵐ θ ∂sourceAngleLaw,
    ∀ I : Finset SourceCoordinate,
      Tendsto (fun s => sourceSamplingUntrimmedTorus I s θ) atTop
        (𝓝 (sourceSamplingLambdaTorus I)) ∧
      ∀ f : C(SourceSamplingTorus,ℝ),
        Tendsto (fun s => ∫ p, f p ∂(sourceSamplingUntrimmedTorus I s θ : Measure SourceSamplingTorus))
          atTop (𝓝 (∫ p, f p ∂(sourceSamplingLambdaTorus I : Measure SourceSamplingTorus))) := by
  filter_upwards [sourceSamplingUntrimmed_weak_event] with θ hθ
  intro I
  have h := FiniteMeasure.tendsto_map_of_tendsto_of_continuous _ _ (hθ I)
    sourceSamplingTorusMap_continuous
  refine ⟨h,fun f => ?_⟩
  exact (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp h)
    (BoundedContinuousFunction.mkOfCompact f)

end
end FiniteFactor

end OAI
