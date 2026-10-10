import OAI.Analysis.FiniteFactor.CrossedProduct.ReferenceOrdered
import OAI.Analysis.FiniteFactor.BiasedPairs.Conull

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter ProbabilityTheory CouplingParameters Finset
open scoped ENNReal
noncomputable section

theorem sourceBiasedRealMeasure_ordered (j : ℕ) (r : SourceCoordinate → Bool) :
    ∀ᵐ z ∂sourceBiasedRealMeasure j r, z ∈ sourceSamplingOrdered := by
  apply (ae_map_iff (sourceBiasedPair_measurable r).aemeasurable sourceSamplingOrdered_measurable).mpr
  filter_upwards [sourceBiasedLaw_ordered j] with ω hω
  intro i
  cases hr : r i
  · simp [sourceBiasedPair,sourceBiasedEndpoint,blockProductEndpoint,endpoint,hr]
  · simpa [sourceBiasedPair,sourceBiasedEndpoint,blockProductEndpoint,endpoint,hr] using hω i

theorem sourceBiasedPrefix_domination_real (j n : ℕ) :
    sourceBiasedRealMeasure j (sourceBiasedPrefixMask n) ≪
      ∑ I ∈ (blockPrefix sourceBlockSize n).powerset, sourceSamplingLambda I := by
  have hh := (sourceBiasedPrefix_ac_reference j n).restrict sourceSamplingOrdered
  rw [Measure.restrict_eq_self_of_ae_mem (sourceBiasedRealMeasure_ordered j _),
    sourceFiniteReference_ordered_mixture] at hh
  exact hh.trans Measure.smul_absolutelyContinuous

/-- Finite-prefix domination by the actual lambda_I measures on the same torus
used for the uncapped invariant-projection identity and weak limits. -/
theorem sourceBiasedPrefix_domination (j n : ℕ) :
    (sourceBiasedTorusMeasure j (sourceBiasedPrefixMask n) : Measure SourceSamplingTorus) ≪
      ∑ I ∈ (blockPrefix sourceBlockSize n).powerset,
        (sourceSamplingLambdaTorus I : Measure SourceSamplingTorus) := by
  have hh := (sourceBiasedPrefix_domination_real j n).map sourceSamplingTorusMap_continuous.measurable
  change _ ≪ _ at hh
  have hm : (∑ I ∈ (blockPrefix sourceBlockSize n).powerset, sourceSamplingLambda I).map sourceSamplingTorusMap =
      ∑ I ∈ (blockPrefix sourceBlockSize n).powerset,
        (sourceSamplingLambdaTorus I : Measure SourceSamplingTorus) := by
    let F := (blockPrefix sourceBlockSize n).powerset
    change (∑ I ∈ F, sourceSamplingLambda I).map sourceSamplingTorusMap =
      ∑ I ∈ F, (sourceSamplingLambdaTorus I : Measure SourceSamplingTorus)
    induction F using Finset.induction_on with
    | empty => simp
    | @insert I F hi ih =>
      rw [Finset.sum_insert hi,Measure.map_add _ _ sourceSamplingTorusMap_continuous.measurable,
        Finset.sum_insert hi,ih]
      rfl
  rw [hm] at hh
  exact hh

end
end FiniteFactor

end OAI
