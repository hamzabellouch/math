import OAI.Analysis.FiniteFactor.OrbitSampling.LambdaRectangles

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

abbrev SourceSamplingPair := (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ)

def sourceSamplingCube : Set SourceSamplingPair :=
  {p | ∀ i, p.1 i ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 i ∈ Set.Icc (0 : ℝ) 1}

theorem sourceSamplingCube_measurable : MeasurableSet sourceSamplingCube := by
  exact sourceSamplingRectangle_measurable _ _ (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc)

instance sourceSamplingUntrimmed_finite (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) : IsFiniteMeasure (sourceSamplingUntrimmed I s θ) := by
  constructor
  unfold sourceSamplingUntrimmed
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem sourceSamplingSummand_cube (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) :
    ∀ᵐ p ∂sourceSamplingSummand I s θ n, p ∈ sourceSamplingCube := by
  apply (ae_map_iff (measurable_id.prodMk (coordinateRotate_preserving θ n).measurable).aemeasurable
    sourceSamplingCube_measurable).mpr
  have hh : ∀ᵐ x ∂sourceSamplingWeightedMeasure I s θ n, ∀ i, x i ∈ Set.Ico (0 : ℝ) 1 :=
    ae_iff.mpr (withDensity_absolutelyContinuous _ _ (ae_iff.mp sourceSamplingHaar_cube))
  filter_upwards [hh] with x hx
  intro i
  exact ⟨⟨(hx i).1,(hx i).2.le⟩,Int.fract_nonneg _,(Int.fract_lt_one _).le⟩

theorem sourceSamplingUntrimmed_cube (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) :
    ∀ᵐ p ∂sourceSamplingUntrimmed I s θ, p ∈ sourceSamplingCube := by
  apply Measure.ae_smul_measure
  rw [ae_iff, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro n hn
  exact ae_iff.mp (sourceSamplingSummand_cube I s θ n)

theorem sourceSamplingLambda_cube (I : Finset SourceCoordinate) :
    ∀ᵐ p ∂sourceSamplingLambda I, p ∈ sourceSamplingCube := by
  apply (ae_map_iff (sourceSamplingLimitMap_measurable I).aemeasurable
    sourceSamplingCube_measurable).mpr
  filter_upwards [ae_restrict_of_ae sourceSamplingPairHaar_cube] with p hp
  intro i
  refine ⟨⟨(hp i).1.1,(hp i).1.2.le⟩,?_⟩
  by_cases hi : i ∈ I
  · simpa [sourceSamplingLimitMap,hi] using And.intro (hp i).2.1 (hp i).2.2.le
  · simpa [sourceSamplingLimitMap,hi] using And.intro (hp i).1.1 (hp i).1.2.le

def sourceSamplingEmptyTest : SourceSamplingRationalTest := ⟨∅,fun _ => ((0,1),(0,1))⟩

theorem sourceSamplingEmptyTest_rectangle :
    sourceSamplingRectangle (sourceSamplingRationalX sourceSamplingEmptyTest)
      (sourceSamplingRationalY sourceSamplingEmptyTest) = sourceSamplingCube := by
  ext p
  simp [sourceSamplingRectangle,sourceSamplingRationalX,sourceSamplingRationalY,
    sourceSamplingRationalEndpoints,sourceSamplingEmptyTest,sourceSamplingCube]

/-- The empty rational test gives actual total-mass convergence. -/
theorem sourceSampling_mass_limit_event : ∀ᵐ θ ∂sourceAngleLaw,
    ∀ I : Finset SourceCoordinate,
      Tendsto (fun s => ((sourceSamplingUntrimmed I s θ) Set.univ).toReal)
        atTop (𝓝 (((sourceSamplingLambda I) Set.univ).toReal)) := by
  filter_upwards [sourceSamplingLambda_rectangle_limit_event] with θ hθ
  intro I
  have h := hθ I sourceSamplingEmptyTest
  rw [sourceSamplingEmptyTest_rectangle] at h
  have hu (s : ℕ) : sourceSamplingUntrimmed I s θ sourceSamplingCube =
      sourceSamplingUntrimmed I s θ Set.univ :=
    measure_congr (by filter_upwards [sourceSamplingUntrimmed_cube I s θ] with p hp; exact propext (iff_true_intro hp))
  have hl : sourceSamplingLambda I sourceSamplingCube = sourceSamplingLambda I Set.univ :=
    measure_congr (by filter_upwards [sourceSamplingLambda_cube I] with p hp; exact propext (iff_true_intro hp))
  simpa only [hu,hl] using h

end
end FiniteFactor

end OAI
