import OAI.Analysis.FiniteFactor.OrbitSampling.PhaseSelfMoment
import OAI.Analysis.FiniteFactor.OrbitSampling.IdealProduct

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

def sourceSamplingProduct (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (n : ℤ) (θ x : SourceCoordinate → ℝ) : ℝ :=
  ∏ i ∈ sourceSamplingPrefix stage,
    samplingOrientedWeight r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
      (E i) (G i) (x i) (Int.fract ((n : ℝ)*θ i))

theorem sourceSamplingProduct_measurable (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) (n : ℤ) :
    Measurable (fun p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ) => sourceSamplingProduct stage r b E G n p.1 p.2) := by
  unfold sourceSamplingProduct
  apply Finset.measurable_prod
  intro i _
  have hm : Measurable (fun p : (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ) =>
      (p.2 i,Int.fract ((n : ℝ)*p.1 i))) :=
    ((measurable_pi_apply i).comp measurable_snd).prodMk
      (sourceFract_measurable.comp (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)))
  exact (samplingOrientedWeight_measurable r (b i) (sourceSamplingWidth stage)
    (sourceSamplingCutoff stage) (E i) (G i) (hE i) (hG i)).comp hm

theorem sourceSamplingProduct_bounds (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (n : ℤ) (θ x : SourceCoordinate → ℝ) :
    0 ≤ sourceSamplingProduct stage r b E G n θ x ∧
    sourceSamplingProduct stage r b E G n θ x ≤
      (max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))^(sourceSamplingPrefix stage).card := by
  have hp := sourceSampling_parameters stage
  have hb (i : SourceCoordinate) := samplingOrientedWeight_bounds r (b i) _ _ (E i) (G i) hp.1 hp.2.2
    (x i) (Int.fract ((n : ℝ)*θ i))
  refine ⟨prod_nonneg (fun i _ => (hb i).1),?_⟩
  calc
    _ ≤ ∏ _i ∈ sourceSamplingPrefix stage, max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)) :=
      prod_le_prod₀ (fun i _ => (hb i).1) (fun i _ => (hb i).2)
    _ = _ := by simp

/-- Exact coordinate factorization under the two actual infinite product laws.
Dependence of the two phases within one coordinate is retained in each factor. -/
theorem sourceSamplingProduct_inner_factorization (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) (n k : ℤ) :
    (∫ x, ∫ θ, sourceSamplingProduct stage r b E G n θ x * sourceSamplingProduct stage r b E G k θ x
      ∂sourceAngleLaw ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) =
    ∏ i ∈ sourceSamplingPrefix stage,
      ∫ s, ∫ θ, samplingOrientedWeight r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
          (E i) (G i) s (Int.fract ((n : ℝ)*θ i)) *
        samplingOrientedWeight r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
          (E i) (G i) s (Int.fract ((k : ℝ)*θ i)) ∂sourceAngleLaw ∂unitIntervalMeasure := by
  let u (i : SourceCoordinate) := samplingOrientedWeight r (b i) (sourceSamplingWidth stage)
    (sourceSamplingCutoff stage) (E i) (G i)
  let F (i : SourceCoordinate) (s a : ℝ) := u i s (Int.fract ((n : ℝ)*a))*u i s (Int.fract ((k : ℝ)*a))
  have hF (i : SourceCoordinate) : Measurable (fun p : ℝ × ℝ => F i p.1 p.2) := by
    have hu := samplingOrientedWeight_measurable r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
      (E i) (G i) (hE i) (hG i)
    exact (hu.comp (measurable_fst.prodMk (sourceFract_measurable.comp (measurable_const.mul measurable_snd)))).mul
      (hu.comp (measurable_fst.prodMk (sourceFract_measurable.comp (measurable_const.mul measurable_snd))))
  calc
    _ = ∫ x, ∏ i ∈ sourceSamplingPrefix stage, ∫ a, F i (x i) a ∂sourceAngleMarginal i
        ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [sourceSamplingProduct,← Finset.prod_mul_distrib]
      exact integral_infinitePi_finset_prod _ _ _
        (fun i => (hF i).comp (measurable_const.prodMk measurable_id))
    _ = ∏ i ∈ sourceSamplingPrefix stage, ∫ s, ∫ a, F i s a ∂sourceAngleMarginal i ∂unitIntervalMeasure :=
      integral_infinitePi_finset_prod _ _ _
        (fun i => (hF i).stronglyMeasurable.integral_prod_right.measurable)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards [] with s
      have hm : Measurable (fun a => F i s a) := (hF i).comp (measurable_const.prodMk measurable_id)
      rw [← sourceAngleLaw_coordinate i,integral_map (measurable_pi_apply i).aemeasurable hm.aestronglyMeasurable]

/-- The actual full-prefix self-pair estimate, with the source's angle
expectation outside the L2 square integral. -/
theorem sourceSamplingProduct_self_moment (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (r : Bool) (b : SourceCoordinate → Bool) (E G : SourceCoordinate → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i))
    (n : ℤ) (hn : n ∈ sourceSamplingPowers stage) :
    (∫ θ, ∫ x, sourceSamplingProduct stage r b E G n θ x ^ 2
      ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure) ∂sourceAngleLaw) ≤
      (2+8*(sourceBlockSize stage : ℝ)^(3/5 : ℝ)*Real.log (sourceBlockSize stage : ℝ))^(sourceSamplingPrefix stage).card := by
  have hint := sampling_square_integrable
    (sourceAngleLaw.prod (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)))
    (fun p => sourceSamplingProduct stage r b E G n p.1 p.2)
    ((max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))^(sourceSamplingPrefix stage).card)
    (sourceSamplingProduct_measurable stage r b E G hE hG n)
    (fun p => sourceSamplingProduct_bounds stage r b E G n p.1 p.2)
  rw [integral_integral_swap hint]
  simp only [pow_two]
  rw [sourceSamplingProduct_inner_factorization stage r b E G hE hG n n]
  calc
    _ ≤ ∏ _i ∈ sourceSamplingPrefix stage,
        (2+8*(sourceBlockSize stage : ℝ)^(3/5 : ℝ)*Real.log (sourceBlockSize stage : ℝ)) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact integral_nonneg (fun s => integral_nonneg (fun θ => mul_self_nonneg _))
      · intro i hi
        have hip : i.1 ≤ stage := by
          have ht := (CouplingParameters.mem_blockPrefix sourceBlockSize (stage+1) i).mp hi
          omega
        simpa only [pow_two] using sourceSampling_phase_self_moment stage hs i hip n hn r (b i)
          (E i) (G i) (hE i) (hG i)
    _ = _ := by simp

end
end FiniteFactor

end OAI
