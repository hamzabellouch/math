import OAI.Analysis.FiniteFactor.OrbitSampling.CutoffMass
import OAI.Analysis.FiniteFactor.OrbitSampling.RectangleApproximation

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

/-- Explicit finite-coordinate rectangle mass of the triangular/diagonal
model. The triangular term retains the actual source weight integral. -/
def sourceSamplingLimitRectangleMass (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest) : ℝ :=
  ∏ i ∈ I ∪ T.1,
    if i ∈ I then
      ∫ s, samplingTestedFirstDensity true (sourceSamplingWidth 0) (sourceSamplingCutoff 0)
        (sourceSamplingRationalX T i) (sourceSamplingRationalY T i) s ∂unitIntervalMeasure
    else (unitIntervalMeasure (sourceSamplingRationalX T i ∩ sourceSamplingRationalY T i)).toReal

/-- Exact finite-coordinate factorization of the first ideal integral. -/
theorem sourceSamplingIdealDensity_integral (I : Finset SourceCoordinate) (stage : ℕ)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    (∫ x, sourceSamplingIdealDensity stage false (fun i => decide (i ∈ I)) E G x ∂sourceSamplingHaar) =
      ∏ i ∈ sourceSamplingPrefix stage, ∫ s,
        samplingTestedFirstDensity (decide (i ∈ I)) (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
          (E i) (G i) s ∂unitIntervalMeasure := by
  exact integral_infinitePi_finset_prod _ _ _ (fun i =>
    samplingTestedFirstDensity_measurable (decide (i ∈ I)) _ _ (E i) (G i) (hE i) (hG i))

/-- Tests and triangular coordinates occupy a fixed finite set. Every other
prefix coordinate contributes its exact retained mass, 1-2α. -/
theorem sourceSamplingIdeal_rectangle_split (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest)
    (stage : ℕ) (hK : I ∪ T.1 ⊆ sourceSamplingPrefix stage) :
    (∫ x, sourceSamplingIdealDensity stage false (fun i => decide (i ∈ I))
      (sourceSamplingRationalX T) (sourceSamplingRationalY T) x ∂sourceSamplingHaar) =
    (∏ i ∈ I ∪ T.1, ∫ s,
      samplingTestedFirstDensity (decide (i ∈ I)) (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        (sourceSamplingRationalX T i) (sourceSamplingRationalY T i) s ∂unitIntervalMeasure) *
    (1-2*sourceSamplingCutoff stage)^((sourceSamplingPrefix stage \ (I ∪ T.1)).card) := by
  rw [sourceSamplingIdealDensity_integral I stage (sourceSamplingRationalX T) (sourceSamplingRationalY T) (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc)]
  let F := fun i => ∫ s, samplingTestedFirstDensity (decide (i ∈ I)) (sourceSamplingWidth stage)
    (sourceSamplingCutoff stage) (sourceSamplingRationalX T i) (sourceSamplingRationalY T i) s ∂unitIntervalMeasure
  have hf (i : SourceCoordinate) (hi : i ∈ sourceSamplingPrefix stage \ (I ∪ T.1)) :
      F i = 1-2*sourceSamplingCutoff stage := by
    have hnot := (Finset.mem_sdiff.mp hi).2
    have hI : i ∉ I := fun h => hnot (Finset.mem_union_left _ h)
    have hT : i ∉ T.1 := fun h => hnot (Finset.mem_union_right _ h)
    simp only [F,decide_eq_false hI,sourceSamplingRationalX,sourceSamplingRationalY,
      sourceSamplingRationalEndpoints,dite_eq_right hT,Rat.cast_zero,Rat.cast_one]
    have hp := sourceSampling_parameters stage
    exact sampling_diagonal_whole_mass _ _ hp.1 hp.2.1 hp.2.2 (sourceSamplingCutoff_le_half stage)
  have hp := Finset.prod_sdiff hK (f := F)
  rw [Finset.prod_congr rfl hf,Finset.prod_const] at hp
  simpa only [mul_comm] using hp.symm

/-- The deterministic ideal product limit includes all growing-prefix cutoff
losses and has exactly the tested diagonal-coordinate limits. -/
theorem sourceSamplingIdeal_rectangle_tendsto (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest) :
    Tendsto (fun stage => ∫ x, sourceSamplingIdealDensity stage false (fun i => decide (i ∈ I))
      (sourceSamplingRationalX T) (sourceSamplingRationalY T) x ∂sourceSamplingHaar)
      atTop (𝓝 (sourceSamplingLimitRectangleMass I T)) := by
  let F := fun stage i => ∫ s, samplingTestedFirstDensity (decide (i ∈ I)) (sourceSamplingWidth stage)
    (sourceSamplingCutoff stage) (sourceSamplingRationalX T i) (sourceSamplingRationalY T i) s ∂unitIntervalMeasure
  have hcoord (i : SourceCoordinate) : Tendsto (fun stage => F stage i) atTop
      (𝓝 (if i ∈ I then ∫ s, samplingTestedFirstDensity true (sourceSamplingWidth 0) (sourceSamplingCutoff 0)
        (sourceSamplingRationalX T i) (sourceSamplingRationalY T i) s ∂unitIntervalMeasure
      else (unitIntervalMeasure (sourceSamplingRationalX T i ∩ sourceSamplingRationalY T i)).toReal)) := by
    by_cases hi : i ∈ I
    · simp only [ite_eq_left hi,F,decide_eq_true hi]
      have he (stage : ℕ) : (∫ s, samplingTestedFirstDensity true (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
          (sourceSamplingRationalX T i) (sourceSamplingRationalY T i) s ∂unitIntervalMeasure) =
        ∫ s, samplingTestedFirstDensity true (sourceSamplingWidth 0) (sourceSamplingCutoff 0)
          (sourceSamplingRationalX T i) (sourceSamplingRationalY T i) s ∂unitIntervalMeasure := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun s => samplingTestedFirstDensity_triangular_parameters _ _ _ _ _ _ _)
      simp_rw [he]
      exact tendsto_const_nhds
    · simp only [ite_eq_right hi,F,decide_eq_false hi]
      exact sourceSampling_diagonal_integral_tendsto _ measurableSet_Icc _ _
  have hfixed := tendsto_finsetProd (I ∪ T.1) (fun i _ => hcoord i)
  have htail := sourceSampling_untested_mass_tendsto
    (fun stage => (sourceSamplingPrefix stage \ (I ∪ T.1)).card)
    (fun stage => Finset.card_le_card Finset.sdiff_subset)
  have hall := hfixed.mul htail
  simp only [mul_one] at hall
  apply hall.congr'
  filter_upwards [sourceSamplingPrefix_eventually_covers (I ∪ T.1)] with stage hstage
  exact (sourceSamplingIdeal_rectangle_split I T stage hstage).symm

/-- Actual untrimmed rational rectangle masses converge to the explicit
triangular/diagonal product value on one conull event for all I and tests. -/
theorem sourceSampling_rectangle_limit_event :
    ∀ᵐ θ ∂sourceAngleLaw, ∀ (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest),
      Tendsto (fun stage => ((sourceSamplingUntrimmed I stage θ)
        (sourceSamplingRectangle (sourceSamplingRationalX T) (sourceSamplingRationalY T))).toReal)
        atTop (𝓝 (sourceSamplingLimitRectangleMass I T)) := by
  filter_upwards [sourceSampling_rectangle_approximation_event] with θ hθ
  intro I T
  have hh := (hθ I T).add (sourceSamplingIdeal_rectangle_tendsto I T)
  simpa only [sub_add_cancel,zero_add] using hh

end
end FiniteFactor

end OAI
