import OAI.Analysis.FiniteFactor.OrbitSampling.LimitMeasure

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

def sourceSamplingLambdaTest (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest)
    (i : SourceCoordinate) (p : ℝ × ℝ) : Prop :=
  if i ∈ I then p.1 ∈ sourceSamplingRationalX T i ∧ p.2 ∈ sourceSamplingRationalY T i ∧ p.1 < p.2
  else p.1 ∈ sourceSamplingRationalX T i ∧ p.1 ∈ sourceSamplingRationalY T i

theorem sourceSamplingLambdaTest_measurable (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest)
    (i : SourceCoordinate) : MeasurableSet {p | sourceSamplingLambdaTest I T i p} := by
  by_cases hi : i ∈ I
  · simp only [sourceSamplingLambdaTest,ite_eq_left hi]
    exact (measurableSet_Icc.preimage measurable_fst).inter
      ((measurableSet_Icc.preimage measurable_snd).inter (measurableSet_lt measurable_fst measurable_snd))
  · simp only [sourceSamplingLambdaTest,ite_eq_right hi]
    exact (measurableSet_Icc.preimage measurable_fst).inter (measurableSet_Icc.preimage measurable_fst)

/-- The finite coordinate conditions are equivalent to restriction by the
triangle and the full cylinder rectangle on the conull Haar cube. -/
theorem sourceSamplingLambdaTest_iff (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest)
    (p : SourceCoordinate → ℝ × ℝ)
    (hp : ∀ i, (p i).1 ∈ Set.Ico (0 : ℝ) 1 ∧ (p i).2 ∈ Set.Ico (0 : ℝ) 1) :
    (∀ i ∈ I ∪ T.1, sourceSamplingLambdaTest I T i (p i)) ↔
      sourceSamplingLimitMap I p ∈ sourceSamplingRectangle (sourceSamplingRationalX T) (sourceSamplingRationalY T) ∧
      p ∈ sourceSamplingTriangleSet I := by
  constructor
  · intro h
    constructor
    · intro i
      by_cases hi : i ∈ I
      · have hh := h i (Finset.mem_union_left _ hi)
        simp only [sourceSamplingLambdaTest,ite_eq_left hi] at hh
        exact ⟨hh.1,by simpa only [sourceSamplingLimitMap,ite_eq_left hi] using hh.2.1⟩
      · by_cases ht : i ∈ T.1
        · have hh := h i (Finset.mem_union_right _ ht)
          simpa only [sourceSamplingLambdaTest,sourceSamplingLimitMap,ite_eq_right hi] using hh
        · have hx : (p i).1 ∈ Set.Icc (0 : ℝ) 1 := ⟨(hp i).1.1,(hp i).1.2.le⟩
          simpa only [sourceSamplingLimitMap,ite_eq_right hi,sourceSamplingRationalX,sourceSamplingRationalY,
            sourceSamplingRationalEndpoints,dite_eq_right ht,Rat.cast_zero,Rat.cast_one] using And.intro hx hx
    · intro i hi
      have hh := h i (Finset.mem_union_left _ hi)
      simp only [sourceSamplingLambdaTest,ite_eq_left hi] at hh
      exact hh.2.2
  · rintro ⟨hrect,htri⟩ i _
    have hh := hrect i
    by_cases hi : i ∈ I
    · simp only [sourceSamplingLambdaTest,ite_eq_left hi]
      exact ⟨hh.1,by simpa only [sourceSamplingLimitMap,ite_eq_left hi] using hh.2,htri i hi⟩
    · simpa only [sourceSamplingLambdaTest,sourceSamplingLimitMap,ite_eq_right hi] using hh

/-- The constructed infinite-coordinate measure has exactly the rectangle
values previously obtained as sampling limits. -/
theorem sourceSamplingLambda_rectangle (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest) :
    ((sourceSamplingLambda I)
      (sourceSamplingRectangle (sourceSamplingRationalX T) (sourceSamplingRationalY T))).toReal =
      sourceSamplingLimitRectangleMass I T := by
  let R := sourceSamplingRectangle (sourceSamplingRationalX T) (sourceSamplingRationalY T)
  let C := sourceSamplingLimitMap I ⁻¹' R ∩ sourceSamplingTriangleSet I
  have hR : MeasurableSet R := sourceSamplingRectangle_measurable _ _
    (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc)
  have hmap := sourceSamplingLimitMap_measurable I
  have hC : MeasurableSet C := (hmap hR).inter (sourceSamplingTriangleSet_measurable I)
  have he : C.indicator (fun _ => (1 : ℝ)) =ᵐ[sourceSamplingPairHaar]
      (fun p => ∏ i ∈ I ∪ T.1, if sourceSamplingLambdaTest I T i (p i) then (1 : ℝ) else 0) := by
    filter_upwards [sourceSamplingPairHaar_cube] with p hp
    simp only [Finset.prod_ite_zero,Finset.prod_const_one,
      sourceSamplingLambdaTest_iff I T p hp,Set.indicator_apply]
    rfl
  rw [sourceSamplingLambda,Measure.map_apply hmap hR,Measure.restrict_apply (hmap hR)]
  change (sourceSamplingPairHaar C).toReal = _
  calc
    _ = ∫ p, C.indicator (fun _ => (1 : ℝ)) p ∂sourceSamplingPairHaar := by
      rw [integral_indicator hC]; simp [measureReal_def]
    _ = ∫ p, ∏ i ∈ I ∪ T.1, if sourceSamplingLambdaTest I T i (p i) then (1 : ℝ) else 0
        ∂sourceSamplingPairHaar := integral_congr_ae he
    _ = ∏ i ∈ I ∪ T.1, ∫ z, (if sourceSamplingLambdaTest I T i z then (1 : ℝ) else 0)
        ∂unitIntervalMeasure.prod unitIntervalMeasure :=
      integral_infinitePi_finset_prod _ _ _ (fun i =>
        Measurable.ite (sourceSamplingLambdaTest_measurable I T i) measurable_const measurable_const)
    _ = _ := by
      rw [sourceSamplingLimitRectangleMass_formula]
      apply Finset.prod_congr rfl
      intro i _
      have hA := sourceSamplingLambdaTest_measurable I T i
      have hh : (∫ z, (if sourceSamplingLambdaTest I T i z then (1 : ℝ) else 0)
          ∂unitIntervalMeasure.prod unitIntervalMeasure) =
          ((unitIntervalMeasure.prod unitIntervalMeasure) {z | sourceSamplingLambdaTest I T i z}).toReal := by
        change (∫ z, {z | sourceSamplingLambdaTest I T i z}.indicator (fun _ => (1 : ℝ)) z
          ∂unitIntervalMeasure.prod unitIntervalMeasure) = _
        rw [integral_indicator hA]; simp [measureReal_def]
      rw [hh]
      by_cases hi : i ∈ I
      · simp only [sourceSamplingLambdaTest,ite_eq_left hi]
      · simp only [sourceSamplingLambdaTest,ite_eq_right hi]
        have heq : {z : ℝ × ℝ | z.1 ∈ sourceSamplingRationalX T i ∧ z.1 ∈ sourceSamplingRationalY T i} =
            (sourceSamplingRationalX T i ∩ sourceSamplingRationalY T i) ×ˢ Set.univ := by ext z; simp
        rw [heq,Measure.prod_prod]
        simp

/-- Actual untrimmed measures converge to the actual source limiting measure
on every rational cylinder rectangle, on a single conull event. -/
theorem sourceSamplingLambda_rectangle_limit_event :
    ∀ᵐ θ ∂sourceAngleLaw, ∀ (I : Finset SourceCoordinate) (T : SourceSamplingRationalTest),
      Tendsto (fun stage => ((sourceSamplingUntrimmed I stage θ)
        (sourceSamplingRectangle (sourceSamplingRationalX T) (sourceSamplingRationalY T))).toReal)
        atTop (𝓝 (((sourceSamplingLambda I)
          (sourceSamplingRectangle (sourceSamplingRationalX T) (sourceSamplingRationalY T))).toReal)) := by
  filter_upwards [sourceSampling_rectangle_limit_event] with θ hθ
  intro I T
  rw [sourceSamplingLambda_rectangle]
  exact hθ I T

end
end FiniteFactor

end OAI
