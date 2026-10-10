import OAI.Analysis.FiniteFactor.OrbitSampling.ProductMoments
import OAI.Analysis.FiniteFactor.OrbitSampling.SingleCorrelation

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

/-- A global bound used only to justify finite-stage integrations. -/
theorem sourceSamplingIdealDensity_bounds (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (x : SourceCoordinate → ℝ) :
    0 ≤ sourceSamplingIdealDensity stage r b E G x ∧
      sourceSamplingIdealDensity stage r b E G x ≤
        (max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))^(sourceSamplingPrefix stage).card := by
  have hp := sourceSampling_parameters stage
  have hb (i : SourceCoordinate) := (sampling_kernel_mean unitIntervalMeasure
    (samplingOrientedWeight r (b i) _ _ (E i) (G i))
    (samplingOrientedWeight_measurable r (b i) _ _ (E i) (G i) (hE i) (hG i))
    (max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))
    (samplingOrientedWeight_bounds r (b i) _ _ (E i) (G i) hp.1 hp.2.2)).2
  refine ⟨prod_nonneg (fun i _ => (hb i (x i)).1),?_⟩
  calc
    _ ≤ ∏ _i ∈ sourceSamplingPrefix stage, max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)) :=
      prod_le_prod₀ (fun i _ => (hb i (x i)).1) (fun i _ => (hb i (x i)).2)
    _ = _ := by simp

/-- Exact mixed factorization for q_n and the actual ideal density on the
full countable Haar space. -/
theorem sourceSamplingProduct_mixed_factorization (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) (n : ℤ) :
    (∫ x, ∫ θ, sourceSamplingProduct stage r b E G n θ x * sourceSamplingIdealDensity stage r b E G x
      ∂sourceAngleLaw ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) =
    ∏ i ∈ sourceSamplingPrefix stage,
      ∫ s, samplingOrientedDensity r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage) (E i) (G i) s *
        (∫ θ, samplingOrientedWeight r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
          (E i) (G i) s (Int.fract ((n : ℝ)*θ i)) ∂sourceAngleLaw) ∂unitIntervalMeasure := by
  let u (i : SourceCoordinate) := samplingOrientedWeight r (b i) (sourceSamplingWidth stage)
    (sourceSamplingCutoff stage) (E i) (G i)
  let a (i : SourceCoordinate) := samplingOrientedDensity r (b i) (sourceSamplingWidth stage)
    (sourceSamplingCutoff stage) (E i) (G i)
  let F (i : SourceCoordinate) (s t : ℝ) := u i s (Int.fract ((n : ℝ)*t))*a i s
  have hF (i : SourceCoordinate) : Measurable (fun p : ℝ × ℝ => F i p.1 p.2) := by
    have hu := samplingOrientedWeight_measurable r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
      (E i) (G i) (hE i) (hG i)
    have ha := samplingOrientedDensity_measurable r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
      (E i) (G i) (hE i) (hG i)
    exact (hu.comp (measurable_fst.prodMk (sourceFract_measurable.comp (measurable_const.mul measurable_snd)))).mul
      (ha.comp measurable_fst)
  calc
    _ = ∫ x, ∏ i ∈ sourceSamplingPrefix stage, ∫ t, F i (x i) t ∂sourceAngleMarginal i
        ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [sourceSamplingProduct,sourceSamplingIdealDensity,← Finset.prod_mul_distrib]
      exact integral_infinitePi_finset_prod _ _ _
        (fun i => (hF i).comp (measurable_const.prodMk measurable_id))
    _ = ∏ i ∈ sourceSamplingPrefix stage, ∫ s, ∫ t, F i s t ∂sourceAngleMarginal i ∂unitIntervalMeasure :=
      integral_infinitePi_finset_prod _ _ _
        (fun i => (hF i).stronglyMeasurable.integral_prod_right.measurable)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards [] with s
      have hm : Measurable (fun t => F i s t) := (hF i).comp (measurable_const.prodMk measurable_id)
      rw [← sourceAngleLaw_coordinate i,integral_map (measurable_pi_apply i).aemeasurable hm.aestronglyMeasurable]
      dsimp [F,u,a]
      rw [integral_mul_const,mul_comm]

/-- Fubini is justified for every finite-stage pair of actual summands. -/
theorem sourceSamplingProduct_pair_integrable (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) (n k : ℤ) :
    Integrable (fun p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ) =>
      sourceSamplingProduct stage r b E G n p.1 p.2*sourceSamplingProduct stage r b E G k p.1 p.2)
      (sourceAngleLaw.prod (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure))) :=
  sampling_bounded_product_integrable _ _ _
    (sourceSamplingProduct_measurable stage r b E G hE hG n)
    (sourceSamplingProduct_measurable stage r b E G hE hG k) _
    (fun p => sourceSamplingProduct_bounds stage r b E G n p.1 p.2)
    (fun p => sourceSamplingProduct_bounds stage r b E G k p.1 p.2)

theorem sourceSamplingProduct_mixed_integrable (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) (n : ℤ) :
    Integrable (fun p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ) =>
      sourceSamplingProduct stage r b E G n p.1 p.2*sourceSamplingIdealDensity stage r b E G p.2)
      (sourceAngleLaw.prod (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure))) :=
  sampling_bounded_product_integrable _ _ _
    (sourceSamplingProduct_measurable stage r b E G hE hG n)
    ((sourceSamplingIdealDensity_measurable stage r b E G hE hG).comp measurable_snd) _
    (fun p => sourceSamplingProduct_bounds stage r b E G n p.1 p.2)
    (fun p => sourceSamplingIdealDensity_bounds stage r b E G hE hG p.2)

end
end FiniteFactor

end OAI
