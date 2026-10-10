import OAI.Analysis.FiniteFactor.OrbitSampling.TriangleLaw
import OAI.Analysis.FiniteFactor.OrbitSampling.IdealRectangleLimit

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

abbrev sourceSamplingPairHaar : Measure (SourceCoordinate → ℝ × ℝ) :=
  Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure.prod unitIntervalMeasure)

def sourceSamplingTriangleSet (I : Finset SourceCoordinate) : Set (SourceCoordinate → ℝ × ℝ) :=
  {p | ∀ i ∈ I, (p i).1 < (p i).2}

def sourceSamplingLimitMap (I : Finset SourceCoordinate) (p : SourceCoordinate → ℝ × ℝ) :
    (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ) :=
  (fun i => (p i).1,fun i => if i ∈ I then (p i).2 else (p i).1)

def sourceSamplingLambda (I : Finset SourceCoordinate) :
    Measure ((SourceCoordinate → ℝ) × (SourceCoordinate → ℝ)) :=
  (sourceSamplingPairHaar.restrict (sourceSamplingTriangleSet I)).map (sourceSamplingLimitMap I)

theorem sourceSamplingTriangleSet_measurable (I : Finset SourceCoordinate) :
    MeasurableSet (sourceSamplingTriangleSet I) := by
  simp only [sourceSamplingTriangleSet,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_lt (measurable_fst.comp (measurable_pi_apply i))
    (measurable_snd.comp (measurable_pi_apply i))

theorem sourceSamplingLimitMap_measurable (I : Finset SourceCoordinate) :
    Measurable (sourceSamplingLimitMap I) := by
  apply Measurable.prodMk
  · exact Measurable.of_eval (fun i => measurable_fst.comp (measurable_pi_apply i))
  · apply Measurable.of_eval
    intro i
    by_cases hi : i ∈ I
    · simpa only [hi,ite_true,Function.comp_def] using measurable_snd.comp (measurable_pi_apply i)
    · simpa only [hi,ite_false,Function.comp_def] using measurable_fst.comp (measurable_pi_apply i)

instance sourceSamplingLambda_finite (I : Finset SourceCoordinate) : IsFiniteMeasure (sourceSamplingLambda I) := by
  unfold sourceSamplingLambda
  infer_instance

theorem sourceSamplingPairHaar_cube : ∀ᵐ p ∂sourceSamplingPairHaar,
    ∀ i, (p i).1 ∈ Set.Ico (0 : ℝ) 1 ∧ (p i).2 ∈ Set.Ico (0 : ℝ) 1 := by
  apply ae_all_iff.mpr
  intro i
  have hp : ∀ᵐ z ∂unitIntervalMeasure.prod unitIntervalMeasure,
      z.1 ∈ Set.Ico (0 : ℝ) 1 ∧ z.2 ∈ Set.Ico (0 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ico.prod measurableSet_Ico)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
    exact ⟨hx,hy⟩
  have hh : ∀ᵐ z ∂sourceSamplingPairHaar.map (fun p => p i),
      z.1 ∈ Set.Ico (0 : ℝ) 1 ∧ z.2 ∈ Set.Ico (0 : ℝ) 1 := by
    rw [Measure.infinitePi_map_eval]
    exact hp
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable hh

/-- The actual limiting measure is carried by ordered pairs. -/
theorem sourceSamplingLambda_ordered (I : Finset SourceCoordinate) :
    ∀ᵐ p ∂sourceSamplingLambda I, ∀ i, p.1 i ≤ p.2 i := by
  have horder : MeasurableSet {p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ) |
      ∀ i, p.1 i ≤ p.2 i} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le
      ((measurable_pi_apply i).comp measurable_fst) ((measurable_pi_apply i).comp measurable_snd))
  apply (ae_map_iff (sourceSamplingLimitMap_measurable I).aemeasurable horder).mpr
  filter_upwards [ae_restrict_mem (sourceSamplingTriangleSet_measurable I)] with p hp
  intro i
  by_cases hi : i ∈ I
  · simpa only [sourceSamplingLimitMap,ite_eq_left hi] using (hp i hi).le
  · simp [sourceSamplingLimitMap,hi]

/-- The finite rectangle formula for the source limit, written using actual
Lebesgue triangular and diagonal masses. -/
theorem sourceSamplingLimitRectangleMass_formula (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest) :
    sourceSamplingLimitRectangleMass I T = ∏ i ∈ I ∪ T.1,
      if i ∈ I then ((unitIntervalMeasure.prod unitIntervalMeasure)
        {p : ℝ × ℝ | p.1 ∈ sourceSamplingRationalX T i ∧
          p.2 ∈ sourceSamplingRationalY T i ∧ p.1 < p.2}).toReal
      else (unitIntervalMeasure (sourceSamplingRationalX T i ∩ sourceSamplingRationalY T i)).toReal := by
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ I
  · simp only [ite_eq_left hi]
    exact samplingTestedFirstDensity_triangular_mass _ _ _ _ measurableSet_Icc measurableSet_Icc
  · simp only [ite_eq_right hi]

end
end FiniteFactor

end OAI
