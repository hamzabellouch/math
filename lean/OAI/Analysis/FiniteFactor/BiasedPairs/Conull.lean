import OAI.Analysis.FiniteFactor.BiasedPairs.Measures
import OAI.Analysis.FiniteFactor.CrossedProduct.ProjectionPositiveConull

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter CouplingParameters
open scoped ENNReal
noncomputable section

theorem sourceBiasedEndpoint_cube (j : ℕ) (r : SourceCoordinate → Bool) :
    ∀ᵐ ω ∂sourceBiasedLaw j, ∀ i, sourceBiasedEndpoint r ω i ∈ Set.Ico (0 : ℝ) 1 := by
  obtain ⟨g,_,_,_,hm,_⟩ := sourceBiasedEndpoint_density j r
  have ha : (sourceBiasedLaw j).map (sourceBiasedEndpoint r) ≪ sourceSamplingHaar := by
    rw [hm]
    exact withDensity_absolutelyContinuous _ _
  exact ae_of_ae_map (sourceBiasedEndpoint_measurable r).aemeasurable
    (ha.ae_le sourceSamplingHaar_cube)

theorem sourceBiasedLaw_ordered (j : ℕ) :
    ∀ᵐ ω ∂sourceBiasedLaw j, ∀ i, (ω i).2.1 ≤ (ω i).2.2 := by
  apply ae_all_iff.mpr
  intro i
  have ha : ∀ᵐ z ∂(stagedCouplingParameters j i.1).labelledCoupling, z.2.1 ≤ z.2.2 := by
    rw [ae_iff]
    change (stagedCouplingParameters j i.1).labelledCoupling {z | z.2.1 ≤ z.2.2}ᶜ = 0
    have hmeas : MeasurableSet {z : Fin 6 × (ℝ × ℝ) | z.2.1 ≤ z.2.2} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    rw [measure_compl hmeas (measure_ne_top _ _),
      measure_univ,labelledCoupling_ordered,tsub_self]
  exact (measurePreserving_eval_infinitePi
    (fun i : SourceCoordinate => (stagedCouplingParameters j i.1).labelledCoupling) i).quasiMeasurePreserving.ae ha

/-- Every mixed law, including nu_j, is carried by the actual ordered representatives. -/
theorem sourceBiasedTorusMeasure_ordered (j : ℕ) (r : SourceCoordinate → Bool) :
    ∀ᵐ z ∂(sourceBiasedTorusMeasure j r : Measure SourceSamplingTorus),
      ∀ i, sourceTorusRepresentative z.1 i ≤ sourceTorusRepresentative z.2 i := by
  have hm : MeasurableSet {z : SourceSamplingTorus | ∀ i,
      sourceTorusRepresentative z.1 i ≤ sourceTorusRepresentative z.2 i} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le
      ((measurable_pi_apply i).comp (sourceTorusRepresentative_preserving.measurable.comp measurable_fst))
      ((measurable_pi_apply i).comp (sourceTorusRepresentative_preserving.measurable.comp measurable_snd))
  apply (ae_map_iff sourceSamplingTorusMap_continuous.measurable.aemeasurable hm).mpr
  apply (ae_map_iff (sourceBiasedPair_measurable r).aemeasurable
    (hm.preimage sourceSamplingTorusMap_continuous.measurable)).mpr
  filter_upwards [sourceBiasedEndpoint_cube j (fun _ => false),sourceBiasedEndpoint_cube j r,
    sourceBiasedLaw_ordered j] with ω hx hy hord
  change ∀ i, sourceTorusRepresentative (sourceTorusQuotient (sourceBiasedEndpoint (fun _ => false) ω)) i ≤
    sourceTorusRepresentative (sourceTorusQuotient (sourceBiasedEndpoint r ω)) i
  rw [sourceTorusRepresentative_quotient _ hx,sourceTorusRepresentative_quotient _ hy]
  intro i
  cases hr : r i
  · simp [sourceBiasedEndpoint,blockProductEndpoint,endpoint,hr]
  · simpa [sourceBiasedEndpoint,blockProductEndpoint,endpoint,hr] using hord i

/-- The same Borel conull set works for both endpoints of every actual biased
or mixed-prefix coupling; there is no new null-set choice for each identity. -/
theorem sourceBiasedTorusMeasure_endpoints_conull (j : ℕ) (r : SourceCoordinate → Bool)
    (Q : Set SourceTorus) (hQ : ∀ᵐ z ∂sourceTorusHaar, z ∈ Q) :
    ∀ᵐ z ∂(sourceBiasedTorusMeasure j r : Measure SourceSamplingTorus), z.1 ∈ Q ∧ z.2 ∈ Q :=
  (ae_of_ae_map (sourceTorusEndpoint_measurable false).aemeasurable
    ((sourceBiasedTorusMeasure_marginal_ac j r false).ae_le hQ)).and
  (ae_of_ae_map (sourceTorusEndpoint_measurable true).aemeasurable
    ((sourceBiasedTorusMeasure_marginal_ac j r true).ae_le hQ))

end
end FiniteFactor

end OAI
