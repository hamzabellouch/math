import OAI.Analysis.FiniteFactor.OrbitSampling.SelfMoment

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Marginal phase domination controls the joint self-pair integral.
This is the source's one-phase step before taking coordinate products. -/
theorem sampling_phase_square_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hdom : μ.map X ≤ (2 : ℝ≥0∞) • unitIntervalMeasure)
    (u : ℝ → ℝ → ℝ) (C : ℝ) (hu : Measurable (fun p : ℝ × ℝ => u p.1 p.2))
    (hb : ∀ s t, 0 ≤ u s t ∧ u s t ≤ C) :
    (∫ s, ∫ ω, u s (X ω)^2 ∂μ ∂unitIntervalMeasure) ≤
      2*(∫ s, ∫ t, u s t^2 ∂unitIntervalMeasure ∂unitIntervalMeasure) := by
  have hΩ : Measurable (fun p : ℝ × Ω => u p.1 (X p.2)) :=
    hu.comp (measurable_fst.prodMk (hX.comp measurable_snd))
  have hiΩ := sampling_square_integrable (unitIntervalMeasure.prod μ) _ C hΩ
    (fun p => hb p.1 (X p.2))
  have hiU := sampling_square_integrable (unitIntervalMeasure.prod unitIntervalMeasure) _ C hu
    (fun p => hb p.1 p.2)
  have hpoint (s : ℝ) : (∫ ω, u s (X ω)^2 ∂μ) ≤ 2*(∫ t, u s t^2 ∂unitIntervalMeasure) := by
    have hm : Measurable (fun t => u s t) := hu.comp (measurable_const.prodMk measurable_id)
    have hi := sampling_square_integrable unitIntervalMeasure _ C hm (hb s)
    have hbig := hi.smul_measure (c := (2 : ℝ≥0∞)) (by norm_num)
    have hle := integral_mono_measure hdom (Eventually.of_forall (fun t => sq_nonneg (u s t))) hbig
    rw [integral_map hX.aemeasurable (hm.pow_const 2).aestronglyMeasurable,
      integral_smul_measure] at hle
    simpa using hle
  calc
    _ ≤ ∫ s, 2*(∫ t, u s t^2 ∂unitIntervalMeasure) ∂unitIntervalMeasure :=
      integral_mono_ae hiΩ.integral_prod_left (hiU.integral_prod_left.const_mul 2)
        (Eventually.of_forall hpoint)
    _ = _ := integral_const_mul _ _

/-- Actual angle expectation of the tested self-pair, at every admissible
selected power, for all source orientations and coordinate types. -/
theorem sourceSampling_phase_self_moment (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (i : SourceCoordinate) (hi : i.1 ≤ stage) (n : ℤ) (hn : n ∈ sourceSamplingPowers stage)
    (r b : Bool) (E G : Set ℝ) (hE : MeasurableSet E) (hG : MeasurableSet G) :
    (∫ s, ∫ θ, samplingOrientedWeight r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
      E G s (Int.fract ((n : ℝ)*θ i)) ^ 2 ∂sourceAngleLaw ∂unitIntervalMeasure) ≤
      2+8*(sourceBlockSize stage : ℝ)^(3/5 : ℝ)*Real.log (sourceBlockSize stage : ℝ) := by
  have hp := sourceSampling_parameters stage
  have hbound := sampling_phase_square_bound sourceAngleLaw (fun θ => Int.fract ((n : ℝ)*θ i))
    (sourceFract_measurable.comp (measurable_const.mul (measurable_pi_apply i)))
    (sourceSampling_phase_domination stage hs i hi n hn)
    (samplingOrientedWeight r b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E G)
    (max 1 (1/(sourceSamplingWidth stage*sourceSamplingCutoff stage)))
    (samplingOrientedWeight_measurable r b _ _ E G hE hG)
    (samplingOrientedWeight_bounds r b _ _ E G hp.1 hp.2.2)
  have hself := sourceSampling_oriented_self_moment stage r b E G hE hG
  exact hbound.trans (by nlinarith)

end
end FiniteFactor

end OAI
