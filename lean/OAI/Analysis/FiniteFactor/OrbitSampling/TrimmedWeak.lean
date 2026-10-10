import OAI.Analysis.FiniteFactor.OrbitSampling.OrderedRestriction
import OAI.Analysis.FiniteFactor.OrbitSampling.CompactTorus

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

def sourceSamplingTrimmedFinite (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) : FiniteMeasure SourceSamplingPair :=
  ⟨sourceSamplingTrimmed I s θ,inferInstance⟩

def sourceSamplingTrimmedTorus (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) : FiniteMeasure SourceSamplingTorus :=
  (sourceSamplingTrimmedFinite I s θ).map sourceSamplingTorusMap

theorem sourceSampling_discarded_tendsto (I : Finset SourceCoordinate)
    (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hmass : Tendsto (fun s => ((sourceSamplingUntrimmed I s θ) Set.univ).toReal)
      atTop (𝓝 (((sourceSamplingLambda I) Set.univ).toReal))) :
    Tendsto (fun s => ((sourceSamplingUntrimmed I s θ) sourceSamplingOrderedᶜ).toReal)
      atTop (𝓝 0) := by
  have hlim := hmass.mul sourceSampling_tail_error_tendsto
  rw [mul_zero] at hlim
  apply squeeze_zero (fun s => ENNReal.toReal_nonneg) _ hlim
  intro s
  have h := ENNReal.toReal_mono (by finiteness)
    (sourceSamplingUntrimmed_discarded_le I s θ hθ)
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity :
    0 ≤ 4*(sourceBlockSize s : ℝ)^(-(sourceBlockSize s : ℝ)/20))] using h

def finiteMeasureRestrict {Ω : Type*} [MeasurableSpace Ω]
    (μ : FiniteMeasure Ω) (A : Set Ω) : FiniteMeasure Ω :=
  ⟨(μ : Measure Ω).restrict A,inferInstance⟩

/-- A restriction whose discarded mass tends to zero has the same finite
weak limit. The norm bound gives the actual error for every test function. -/
theorem finiteMeasure_restrict_tendsto {Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    (μ : ℕ → FiniteMeasure Ω) (ν : FiniteMeasure Ω) (A : Set Ω) (hA : MeasurableSet A)
    (hμ : Tendsto μ atTop (𝓝 ν))
    (hloss : Tendsto (fun n => ((μ n : Measure Ω) Aᶜ).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => finiteMeasureRestrict (μ n) A)
      atTop (𝓝 ν) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  have hf := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hμ f
  have he : Tendsto (fun n => ∫ x in Aᶜ, f x ∂(μ n : Measure Ω)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hb := hloss.const_mul ‖f‖
    rw [mul_zero] at hb
    apply squeeze_zero (fun n => norm_nonneg _) _ hb
    intro n
    have hh := norm_integral_le_of_norm_le_const
      (μ := (μ n : Measure Ω).restrict Aᶜ)
      (Eventually.of_forall (fun x => f.norm_coe_le_norm x))
    simpa only [measureReal_def,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter] using hh
  have hsub := hf.sub he
  rw [sub_zero] at hsub
  convert hsub using 1
  funext n
  exact (eq_sub_iff_add_eq.mpr (integral_add_compl (μ := (μ n : Measure Ω)) hA (f.integrable (μ := (μ n : Measure Ω)))))

/-- Actual ordered measures have the same compact-torus weak limit, for
all continuous tests, on one probability-one angle event. -/
theorem sourceSamplingTrimmed_weak_event : ∀ᵐ θ ∂sourceAngleLaw,
    ∀ I : Finset SourceCoordinate,
      Tendsto (fun s => sourceSamplingTrimmedFinite I s θ) atTop (𝓝 (sourceSamplingLambdaFinite I)) ∧
      Tendsto (fun s => sourceSamplingTrimmedTorus I s θ) atTop (𝓝 (sourceSamplingLambdaTorus I)) ∧
      ∀ f : C(SourceSamplingTorus,ℝ),
        Tendsto (fun s => ∫ p, f p ∂(sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus))
          atTop (𝓝 (∫ p, f p ∂(sourceSamplingLambdaTorus I : Measure SourceSamplingTorus))) := by
  filter_upwards [sourceSamplingUntrimmed_weak_event,sourceSampling_mass_limit_event,sourceAngleLaw_admissible]
    with θ hw hm ha
  intro I
  have h := finiteMeasure_restrict_tendsto (fun s => sourceSamplingUntrimmedFinite I s θ)
    (sourceSamplingLambdaFinite I) sourceSamplingOrdered sourceSamplingOrdered_measurable
    (hw I) (sourceSampling_discarded_tendsto I θ ha (hm I))
  have ht := FiniteMeasure.tendsto_map_of_tendsto_of_continuous _ _ h sourceSamplingTorusMap_continuous
  refine ⟨h,ht,fun f => ?_⟩
  exact (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp ht) (BoundedContinuousFunction.mkOfCompact f)

end
end FiniteFactor

end OAI
