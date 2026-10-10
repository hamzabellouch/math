import OAI.Analysis.FiniteFactor.Sampling.FirstInterval
import OAI.Analysis.FiniteFactor.OrbitSampling.Weights

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section

/-- Rectangle discrepancy passes exactly to the first-oriented tested weights. -/
theorem samplingTestedFirst_pair_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    [NullSingletonClass (μ.map X)] [NullSingletonClass (μ.map Y)]
    (δ : ℝ) (hrect : ∀ a b c d : ℝ,
      |(μ {ω | X ω ∈ Set.Icc a b ∧ Y ω ∈ Set.Icc c d}).toReal -
        (unitIntervalMeasure (Set.Icc a b)).toReal*(unitIntervalMeasure (Set.Icc c d)).toReal| ≤ δ)
    (b : Bool) (h α : ℝ) (E : Set ℝ) (a c s : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hs : s ∈ Set.Ico (0 : ℝ) 1) :
    |(∫ ω, samplingTestedFirstWeight b h α E (Set.Icc a c) s (X ω) *
        samplingTestedFirstWeight b h α E (Set.Icc a c) s (Y ω) ∂μ) -
      samplingTestedFirstDensity b h α E (Set.Icc a c) s ^ 2| ≤
      δ*(if s ∈ E then samplingFirstHeight b h α s else 0)^2 := by
  have : NullSingletonClass unitIntervalMeasure := by unfold unitIntervalMeasure; infer_instance
  let A := max 0 (a-s)
  let B := min (samplingFirstLength b h s) (c-s)
  let C := if s ∈ E then samplingFirstHeight b h α s else 0
  let D := Set.Icc A B
  have hrep (ν : Measure ℝ) [NullSingletonClass ν] :
      samplingTestedFirstWeight b h α E (Set.Icc a c) s =ᵐ[ν] D.indicator (fun _ => C) :=
    samplingTestedFirstWeight_closed_interval_ae ν b h α E a c s hh hh1 hα hs
  have hprod : (∫ ω, samplingTestedFirstWeight b h α E (Set.Icc a c) s (X ω) *
        samplingTestedFirstWeight b h α E (Set.Icc a c) s (Y ω) ∂μ) =
      C^2*(μ {ω | X ω ∈ D ∧ Y ω ∈ D}).toReal := by
    calc
      _ = ∫ ω, ({ω | X ω ∈ D ∧ Y ω ∈ D}).indicator (fun _ => C^2) ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_of_ae_map hX.aemeasurable (hrep (μ.map X)),
          ae_of_ae_map hY.aemeasurable (hrep (μ.map Y))] with ω hx hy
        rw [hx,hy]
        simp only [Set.indicator,Set.mem_ofPred_eq]
        split_ifs <;> simp_all [pow_two]
      _ = _ := by
        have hD : MeasurableSet {ω | X ω ∈ D ∧ Y ω ∈ D} :=
          (measurableSet_Icc.preimage hX).inter (measurableSet_Icc.preimage hY)
        rw [integral_indicator hD]
        simp [integral_const,measureReal_def,smul_eq_mul,mul_comm,D]
  have hmean : samplingTestedFirstDensity b h α E (Set.Icc a c) s =
      C*(unitIntervalMeasure D).toReal := by
    unfold samplingTestedFirstDensity
    rw [integral_congr_ae (hrep unitIntervalMeasure),integral_indicator measurableSet_Icc]
    simp [integral_const,measureReal_def,smul_eq_mul,mul_comm,D]
  rw [hprod,hmean]
  calc
    _ = C^2*|(μ {ω | X ω ∈ D ∧ Y ω ∈ D}).toReal -
        (unitIntervalMeasure D).toReal*(unitIntervalMeasure D).toReal| := by
      calc
        _ = |C^2*((μ {ω | X ω ∈ D ∧ Y ω ∈ D}).toReal -
            (unitIntervalMeasure D).toReal*(unitIntervalMeasure D).toReal)| := by congr 1; ring
        _ = _ := by rw [abs_mul,abs_of_nonneg (sq_nonneg C)]
    _ ≤ C^2*δ := mul_le_mul_of_nonneg_left (hrect A B A B) (sq_nonneg C)
    _ = _ := by ring

/-- The actual selected phase laws are atomless, despite possible dependence
between two phases. Only their already proved marginal domination is used. -/
theorem sourceSampling_phase_null_singletons (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (i : SourceCoordinate) (hi : i.1 ≤ stage) (n : ℤ) (hn : n ∈ sourceSamplingPowers stage) :
    NullSingletonClass (sourceAngleLaw.map (fun θ => Int.fract ((n : ℝ)*θ i))) := by
  have : NullSingletonClass unitIntervalMeasure := by unfold unitIntervalMeasure; infer_instance
  constructor
  intro x
  have hdom := sourceSampling_phase_domination stage hs i hi n hn
  exact le_antisymm ((hdom {x}).trans_eq (by simp)) bot_le

/-- Actual first-tested pair discrepancy, with all probabilistic assumptions
discharged by the source's deterministic separated powers. -/
theorem sourceSampling_first_pair_bound (stage : ℕ) (hs : 200000 ≤ sourceBlockSize stage)
    (i : SourceCoordinate) (hi : i.1 ≤ stage) (n n' : ℤ)
    (hn : n ∈ sourceSamplingPowers stage) (hn' : n' ∈ sourceSamplingPowers stage) (hne : n ≠ n')
    (b : Bool) (E : Set ℝ) (a c s : ℝ) (hsx : s ∈ Set.Ico (0 : ℝ) 1) :
    |(∫ θ, samplingTestedFirstWeight b (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        E (Set.Icc a c) s (Int.fract ((n : ℝ)*θ i)) *
        samplingTestedFirstWeight b (sourceSamplingWidth stage) (sourceSamplingCutoff stage)
        E (Set.Icc a c) s (Int.fract ((n' : ℝ)*θ i)) ∂sourceAngleLaw) -
      samplingTestedFirstDensity b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) E (Set.Icc a c) s ^ 2| ≤
      (26*(sourceBlockSize stage : ℝ)^(-80 : ℝ))*
        (if s ∈ E then samplingFirstHeight b (sourceSamplingWidth stage) (sourceSamplingCutoff stage) s else 0)^2 := by
  have := sourceSampling_phase_null_singletons stage hs i hi n hn
  have := sourceSampling_phase_null_singletons stage hs i hi n' hn'
  have hp := sourceSampling_parameters stage
  exact samplingTestedFirst_pair_bound sourceAngleLaw
    (fun θ => Int.fract ((n : ℝ)*θ i)) (fun θ => Int.fract ((n' : ℝ)*θ i))
    (sourceFract_measurable.comp (measurable_const.mul (measurable_pi_apply i)))
    (sourceFract_measurable.comp (measurable_const.mul (measurable_pi_apply i))) _
    (sourceSampling_rectangle_bound stage hs i hi n n' hn hn' hne)
    b _ _ E a c s hp.1 hp.2.1 hp.2.2 hsx

end
end FiniteFactor

end OAI
