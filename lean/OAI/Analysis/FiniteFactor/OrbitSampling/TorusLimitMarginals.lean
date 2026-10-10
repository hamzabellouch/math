import OAI.Analysis.FiniteFactor.OrbitSampling.TorusMarginals
import OAI.Analysis.FiniteFactor.OrbitSampling.LambdaMarginals
import OAI.Analysis.FiniteFactor.OrbitSampling.TorusSupport

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- The actual compact-torus limiting marginals are dominated by product
Haar, the exact absolute continuity premise needed in the Lusin transfer. -/
theorem sourceSamplingLambdaTorus_marginal_le (I : Finset SourceCoordinate) (r : Bool) :
    (sourceSamplingLambdaTorus I : Measure SourceSamplingTorus).map (sourceTorusEndpoint r) ≤ sourceTorusHaar := by
  have he : sourceTorusEndpoint r ∘ sourceSamplingTorusMap = sourceTorusQuotient ∘ sourceSamplingEndpoint r := by
    funext p
    cases r <;> rfl
  change ((sourceSamplingLambda I).map sourceSamplingTorusMap).map (sourceTorusEndpoint r) ≤ _
  rw [Measure.map_map (sourceTorusEndpoint_measurable r) sourceSamplingTorusMap_continuous.measurable,he,
    ← Measure.map_map sourceTorusQuotient_preserving.measurable (sourceSamplingEndpoint_measurable r)]
  have h := Measure.map_mono (sourceSamplingLambda_marginal_le I r) sourceTorusQuotient_preserving.measurable
  rwa [sourceTorusQuotient_preserving.map_eq] at h

theorem sourceSamplingLambdaTorus_marginal_ac (I : Finset SourceCoordinate) (r : Bool) :
    (sourceSamplingLambdaTorus I : Measure SourceSamplingTorus).map (sourceTorusEndpoint r) ≪ sourceTorusHaar :=
  Measure.absolutelyContinuous_of_le (sourceSamplingLambdaTorus_marginal_le I r)

theorem sourceSamplingLambda_representatives (I : Finset SourceCoordinate) :
    ∀ᵐ p ∂sourceSamplingLambda I, sourceSamplingPairRepresentative (sourceSamplingTorusMap p) = p := by
  have hmeas : MeasurableSet {p : SourceSamplingPair |
      sourceSamplingPairRepresentative (sourceSamplingTorusMap p) = p} :=
    measurableSet_eq_fun (sourceSamplingPairRepresentative_measurable.comp sourceSamplingTorusMap_continuous.measurable)
      measurable_id
  apply (ae_map_iff (sourceSamplingLimitMap_measurable I).aemeasurable hmeas).mpr
  filter_upwards [ae_restrict_of_ae sourceSamplingPairHaar_cube] with p hp
  apply Prod.ext
  · exact sourceTorusRepresentative_quotient _ (fun i => (hp i).1)
  · apply sourceTorusRepresentative_quotient
    intro i
    by_cases hi : i ∈ I
    · simpa only [sourceSamplingLimitMap,ite_eq_left hi] using (hp i).2
    · simpa only [sourceSamplingLimitMap,ite_eq_right hi] using (hp i).1

/-- The actual limiting torus measure has the same representative order
as the trimmed measures. No closure of the order set in torus topology is assumed. -/
theorem sourceSamplingLambdaTorus_ordered (I : Finset SourceCoordinate) :
    ∀ᵐ p ∂(sourceSamplingLambdaTorus I : Measure SourceSamplingTorus),
      ∀ i, sourceTorusRepresentative p.1 i ≤ sourceTorusRepresentative p.2 i := by
  have hmeas : MeasurableSet {p : SourceSamplingTorus |
      ∀ i, sourceTorusRepresentative p.1 i ≤ sourceTorusRepresentative p.2 i} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le
      ((measurable_pi_apply i).comp (sourceTorusRepresentative_preserving.measurable.comp measurable_fst))
      ((measurable_pi_apply i).comp (sourceTorusRepresentative_preserving.measurable.comp measurable_snd)))
  apply (ae_map_iff sourceSamplingTorusMap_continuous.measurable.aemeasurable hmeas).mpr
  filter_upwards [sourceSamplingLambda_ordered I,sourceSamplingLambda_representatives I] with p hp he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  change sourceTorusRepresentative (sourceTorusQuotient p.1) = p.1 at h1
  change sourceTorusRepresentative (sourceTorusQuotient p.2) = p.2 at h2
  change ∀ i, sourceTorusRepresentative (sourceTorusQuotient p.1) i ≤ sourceTorusRepresentative (sourceTorusQuotient p.2) i
  rw [h1,h2]
  exact hp

end
end FiniteFactor

end OAI
