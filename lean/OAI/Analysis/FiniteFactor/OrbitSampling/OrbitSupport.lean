import OAI.Analysis.FiniteFactor.OrbitSampling.OrderedRestriction

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

def sourceSamplingPositiveOrbits (s : ℕ) (θ : SourceCoordinate → ℝ) : Set SourceSamplingPair :=
  {p | ∃ n ∈ sourceSamplingPowers s, 0 < n ∧ p.2 = coordinateRotate θ n p.1}

theorem sourceSamplingPositiveOrbits_measurable (s : ℕ) (θ : SourceCoordinate → ℝ) :
    MeasurableSet (sourceSamplingPositiveOrbits s θ) := by
  simp only [sourceSamplingPositiveOrbits,Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro n
  by_cases hn : n ∈ sourceSamplingPowers s
  · simp only [hn,true_and]
    by_cases hp : 0 < n
    · simp only [hp,true_and]
      exact measurableSet_eq_fun measurable_snd ((coordinateRotate_preserving θ n).measurable.comp measurable_fst)
    · simp [hp]
  · simp [hn]

theorem sourceSamplingSummand_positive_orbit (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) (hn : n ∈ sourceSamplingPowers s) :
    ∀ᵐ p ∂sourceSamplingSummand I s θ n, p ∈ sourceSamplingPositiveOrbits s θ := by
  apply (ae_map_iff (measurable_id.prodMk (coordinateRotate_preserving θ n).measurable).aemeasurable
    (sourceSamplingPositiveOrbits_measurable s θ)).mpr
  exact Eventually.of_forall (fun x => ⟨n,hn,(sourceSamplingPowers_positive s n hn).1,rfl⟩)

/-- Trimming preserves the constructed finite set of strictly positive
orbit powers while imposing coordinatewise order everywhere. -/
theorem sourceSamplingTrimmed_orbits (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) : ∀ᵐ p ∂sourceSamplingTrimmed I s θ,
      (∀ i, p.1 i ≤ p.2 i) ∧ ∃ n ∈ sourceSamplingPowers s, 0 < n ∧ p.2 = coordinateRotate θ n p.1 := by
  have hu : ∀ᵐ p ∂sourceSamplingUntrimmed I s θ, p ∈ sourceSamplingPositiveOrbits s θ := by
    apply Measure.ae_smul_measure
    rw [ae_iff,Measure.finsetSum_apply]
    exact Finset.sum_eq_zero (fun n hn => ae_iff.mp (sourceSamplingSummand_positive_orbit I s θ n hn))
  filter_upwards [sourceSamplingTrimmed_ordered I s θ,ae_restrict_of_ae hu] with p ho hp
  exact ⟨ho,hp⟩

end
end FiniteFactor

end OAI
