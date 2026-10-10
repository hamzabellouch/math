import OAI.Analysis.FiniteFactor.Sampling.OrientedMoments

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

/-- The actual source prefix dimension, including the current block. -/
theorem sourceSamplingPrefix_card (stage : ℕ) :
    (sourceSamplingPrefix stage).card = (sourceStageState stage).d+sourceBlockSize stage := by
  unfold sourceSamplingPrefix CouplingParameters.blockPrefix
  simp only [Finset.card_sigma,Finset.card_univ,Fintype.card_fin]
  change (∑ i ∈ range (stage+1), (sourceStage i).m) = _
  rw [sum_range_succ,← sourceStage_previous_size]
  rfl

theorem sourceSamplingPrefix_card_bound (stage : ℕ) :
    ((sourceSamplingPrefix stage).card : ℝ) ≤ (101/100 : ℝ)*sourceBlockSize stage := by
  rw [sourceSamplingPrefix_card,Nat.cast_add]
  have hp := (sourceStage stage).previous_size
  change ((sourceStageState stage).d : ℝ) ≤ (sourceBlockSize stage : ℝ)/100 at hp
  linarith

/-- The small quadratic coordinate errors stay bounded in the growing prefix. -/
theorem sourceSampling_prefix_quadratic_budget (stage : ℕ) :
    ((sourceSamplingPrefix stage).card : ℝ)*(4*(sourceBlockSize stage : ℝ)^(-6/5 : ℝ)) ≤ 5 := by
  have hm := sourceBlockSize_pos stage
  have hm1 : (1 : ℝ) ≤ sourceBlockSize stage := by
    have hh : (100 : ℝ) ≤ sourceBlockSize stage := by exact_mod_cast (sourceStage stage).m_ge_100
    linarith
  have he : (sourceBlockSize stage : ℝ)*(sourceBlockSize stage : ℝ)^(-6/5 : ℝ) =
      (sourceBlockSize stage : ℝ)^(-1/5 : ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one (sourceBlockSize stage : ℝ)]
    rw [← Real.rpow_add hm]
    norm_num
  have hp : (sourceBlockSize stage : ℝ)^(-1/5 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hm1 (by norm_num)
  calc
    _ ≤ ((101/100 : ℝ)*sourceBlockSize stage)*(4*(sourceBlockSize stage : ℝ)^(-6/5 : ℝ)) :=
      mul_le_mul_of_nonneg_right (sourceSamplingPrefix_card_bound stage) (by positivity)
    _ = (101/25 : ℝ)*(sourceBlockSize stage : ℝ)^(-1/5 : ℝ) := by rw [← he]; ring
    _ ≤ 5 := by linarith

def sourceSamplingIdealDensity (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (x : SourceCoordinate → ℝ) : ℝ :=
  ∏ i ∈ sourceSamplingPrefix stage,
    samplingOrientedDensity r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage) (E i) (G i) (x i)

theorem sourceSamplingIdealDensity_measurable (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    Measurable (sourceSamplingIdealDensity stage r b E G) :=
  Finset.measurable_prod _ (fun i _ =>
    (samplingOrientedDensity_measurable r (b i) _ _ (E i) (G i) (hE i) (hG i)).comp (measurable_pi_apply i))

/-- Exact product factorization of the ideal marginal's quadratic moment. -/
theorem sourceSamplingIdealDensity_square (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    (∫ x, sourceSamplingIdealDensity stage r b E G x ^ 2
      ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) =
      ∏ i ∈ sourceSamplingPrefix stage,
        ∫ s, samplingOrientedDensity r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage) (E i) (G i) s ^ 2
          ∂unitIntervalMeasure := by
  simp only [sourceSamplingIdealDensity,← Finset.prod_pow]
  exact integral_infinitePi_finset_prod _ _ _ (fun i =>
    (samplingOrientedDensity_measurable r (b i) _ _ (E i) (G i) (hE i) (hG i)).pow_const 2)

/-- Uniform-in-stage ideal marginal bound. The second orientation uses the
quadratic cancellation established for the actual cutoff diagonal density. -/
theorem sourceSamplingIdealDensity_uniform_square (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    (∫ x, sourceSamplingIdealDensity stage r b E G x ^ 2
      ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) ≤ Real.exp 5 := by
  rw [sourceSamplingIdealDensity_square stage r b E G hE hG,← Finset.prod_coe_sort]
  have he := product_energy_le_exp
    (fun i : sourceSamplingPrefix stage => ∫ s, samplingOrientedDensity r (b i)
      (sourceSamplingWidth stage) (sourceSamplingCutoff stage) (E i) (G i) s ^ 2 ∂unitIntervalMeasure)
    (fun _ : sourceSamplingPrefix stage => 4*(sourceBlockSize stage : ℝ)^(-6/5 : ℝ))
    (fun i => integral_nonneg (fun _ => sq_nonneg _))
    (fun i => (sourceSampling_oriented_moment stage r (b i) (E i) (G i) (hE i) (hG i)).2)
  apply he.trans
  apply Real.exp_le_exp.mpr
  simpa using sourceSampling_prefix_quadratic_budget stage

/-- Each ideal marginal is genuinely in L2; the preceding integral bound is
therefore a norm bound, not an integral of a nonintegrable function. -/
theorem sourceSamplingIdealDensity_memLp (stage : ℕ) (r : Bool) (b : SourceCoordinate → Bool)
    (E G : SourceCoordinate → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (hG : ∀ i, MeasurableSet (G i)) :
    MemLp (sourceSamplingIdealDensity stage r b E G) 2
      (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) := by
  let C := max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage))
  have hp := sourceSampling_parameters stage
  have hb (i : SourceCoordinate) (s : ℝ) :
      0 ≤ samplingOrientedDensity r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage) (E i) (G i) s ∧
      samplingOrientedDensity r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage) (E i) (G i) s ≤ C := by
    have hm : Measurable (samplingOrientedWeight r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage) (E i) (G i) s) :=
      (samplingOrientedWeight_measurable r (b i) _ _ (E i) (G i) (hE i) (hG i)).comp
        (measurable_const.prodMk measurable_id)
    have hw := samplingOrientedWeight_bounds r (b i) _ _ (E i) (G i) hp.1 hp.2.2 s
    have hi : Integrable (samplingOrientedWeight r (b i) (sourceSamplingWidth stage) (sourceSamplingCutoff stage) (E i) (G i) s)
        unitIntervalMeasure := (integrable_const C).mono' hm.aestronglyMeasurable
      (Eventually.of_forall (fun t => by rw [Real.norm_eq_abs,abs_of_nonneg (hw t).1]; exact (hw t).2))
    refine ⟨integral_nonneg (fun t => (hw t).1),?_⟩
    simpa [samplingOrientedDensity] using integral_mono_ae hi (integrable_const C)
      (Eventually.of_forall (fun t => (hw t).2))
  apply MemLp.of_bound (sourceSamplingIdealDensity_measurable stage r b E G hE hG).aestronglyMeasurable
    (C^(sourceSamplingPrefix stage).card)
  apply Eventually.of_forall
  intro x
  have hnon : 0 ≤ sourceSamplingIdealDensity stage r b E G x := prod_nonneg (fun i _ => (hb i (x i)).1)
  rw [Real.norm_eq_abs,abs_of_nonneg hnon]
  calc
    _ ≤ ∏ _i ∈ sourceSamplingPrefix stage, C :=
      prod_le_prod₀ (fun i _ => (hb i (x i)).1) (fun i _ => (hb i (x i)).2)
    _ = _ := by simp

end
end FiniteFactor

end OAI
