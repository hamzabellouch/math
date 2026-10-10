import OAI.Analysis.FiniteFactor.CrossedProduct.TorusModel
import OAI.Analysis.FiniteFactor.OrbitSampling.OrbitSupport
import OAI.Analysis.FiniteFactor.OrbitSampling.TrimmedWeak

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Classical
noncomputable section

def sourceSamplingPairRepresentative (z : SourceSamplingTorus) : SourceSamplingPair :=
  (sourceTorusRepresentative z.1,sourceTorusRepresentative z.2)

theorem sourceSamplingPairRepresentative_measurable : Measurable sourceSamplingPairRepresentative :=
  (sourceTorusRepresentative_preserving.measurable.comp measurable_fst).prodMk
    (sourceTorusRepresentative_preserving.measurable.comp measurable_snd)

def sourceTorusRotate (θ : SourceCoordinate → ℝ) (n : ℤ) (z : SourceTorus) : SourceTorus :=
  fun i => z i + n • (θ i : UnitAddCircle)

theorem sourceTorusRotate_continuous (θ : SourceCoordinate → ℝ) (n : ℤ) : Continuous (sourceTorusRotate θ n) :=
  continuous_pi (fun i => (continuous_apply i).add continuous_const)

theorem sourceTorusQuotient_rotate (θ x : SourceCoordinate → ℝ) (n : ℤ) :
    sourceTorusQuotient (coordinateRotate θ n x) = sourceTorusRotate θ n (sourceTorusQuotient x) := by
  funext i
  simp only [sourceTorusQuotient,coordinateRotate,sourceTorusRotate,AddCircle.coe_fract,
    AddCircle.coe_add,← zsmul_eq_mul,AddCircle.coe_zsmul]

/-- The chosen real representatives recover the actual orbit measures;
closed-cube endpoints are not silently identified with distinct real points. -/
theorem sourceSamplingTrimmed_representatives (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) : ∀ᵐ p ∂sourceSamplingTrimmed I s θ,
      sourceSamplingPairRepresentative (sourceSamplingTorusMap p) = p := by
  have hmeas : MeasurableSet {p : SourceSamplingPair |
      sourceSamplingPairRepresentative (sourceSamplingTorusMap p) = p} :=
    measurableSet_eq_fun (sourceSamplingPairRepresentative_measurable.comp sourceSamplingTorusMap_continuous.measurable)
      measurable_id
  have hu : ∀ᵐ p ∂sourceSamplingUntrimmed I s θ,
      sourceSamplingPairRepresentative (sourceSamplingTorusMap p) = p := by
    apply Measure.ae_smul_measure
    rw [ae_iff,Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro n hn
    apply ae_iff.mp
    apply (ae_map_iff (measurable_id.prodMk (coordinateRotate_preserving θ n).measurable).aemeasurable hmeas).mpr
    have hh : ∀ᵐ x ∂sourceSamplingWeightedMeasure I s θ n, ∀ i, x i ∈ Set.Ico (0 : ℝ) 1 :=
      ae_iff.mpr (withDensity_absolutelyContinuous _ _ (ae_iff.mp sourceSamplingHaar_cube))
    filter_upwards [hh] with x hx
    apply Prod.ext
    · exact sourceTorusRepresentative_quotient x hx
    · exact sourceTorusRepresentative_quotient _ (fun i => ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩)
  exact ae_restrict_of_ae hu

def sourceSamplingTorusOrderedOrbits (s : ℕ) (θ : SourceCoordinate → ℝ) : Set SourceSamplingTorus :=
  {p | (∀ i, sourceTorusRepresentative p.1 i ≤ sourceTorusRepresentative p.2 i) ∧
    ∃ n ∈ sourceSamplingPowers s, 0 < n ∧ p.2 = sourceTorusRotate θ n p.1}

theorem sourceSamplingTorusOrderedOrbits_measurable (s : ℕ) (θ : SourceCoordinate → ℝ) :
    MeasurableSet (sourceSamplingTorusOrderedOrbits s θ) := by
  change MeasurableSet ({p : SourceSamplingTorus | ∀ i, sourceTorusRepresentative p.1 i ≤ sourceTorusRepresentative p.2 i} ∩
    {p : SourceSamplingTorus | ∃ n ∈ sourceSamplingPowers s, 0 < n ∧ p.2 = sourceTorusRotate θ n p.1})
  apply MeasurableSet.inter
  · simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le
      ((measurable_pi_apply i).comp (sourceTorusRepresentative_preserving.measurable.comp measurable_fst))
      ((measurable_pi_apply i).comp (sourceTorusRepresentative_preserving.measurable.comp measurable_snd)))
  · simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro n
    by_cases hn : n ∈ sourceSamplingPowers s ∧ 0 < n
    · simp only [hn.1,hn.2,true_and]
      exact measurableSet_eq_fun measurable_snd ((sourceTorusRotate_continuous θ n).measurable.comp measurable_fst)
    · have he : {p : SourceSamplingTorus | n ∈ sourceSamplingPowers s ∧ 0 < n ∧ p.2 = sourceTorusRotate θ n p.1} = ∅ := by
        ext p; simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]; tauto
      rw [he]
      exact MeasurableSet.empty

/-- Actual compact-torus support: representatives are ordered, and each pair
lies on one of the constructed finitely many strictly positive rotation graphs. -/
theorem sourceSamplingTrimmed_torus_orbits (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) :
    ∀ᵐ p ∂(sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus),
      (∀ i, sourceTorusRepresentative p.1 i ≤ sourceTorusRepresentative p.2 i) ∧
      ∃ n ∈ sourceSamplingPowers s, 0 < n ∧ p.2 = sourceTorusRotate θ n p.1 := by
  apply (ae_map_iff sourceSamplingTorusMap_continuous.measurable.aemeasurable
    (sourceSamplingTorusOrderedOrbits_measurable s θ)).mpr
  filter_upwards [sourceSamplingTrimmed_orbits I s θ,sourceSamplingTrimmed_representatives I s θ] with p hp he
  refine ⟨?_,?_⟩
  · have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    change sourceTorusRepresentative (sourceTorusQuotient p.1) = p.1 at h1
    change sourceTorusRepresentative (sourceTorusQuotient p.2) = p.2 at h2
    change ∀ i, sourceTorusRepresentative (sourceTorusQuotient p.1) i ≤ sourceTorusRepresentative (sourceTorusQuotient p.2) i
    rw [h1,h2]
    exact hp.1
  · obtain ⟨n,hn,hpos,hrot⟩ := hp.2
    refine ⟨n,hn,hpos,?_⟩
    change sourceTorusQuotient p.2 = sourceTorusRotate θ n (sourceTorusQuotient p.1)
    rw [hrot]
    exact sourceTorusQuotient_rotate θ p.1 n

end
end FiniteFactor

end OAI
