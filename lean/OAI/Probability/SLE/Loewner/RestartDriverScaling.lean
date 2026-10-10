import OAI.Probability.SLE.Loewner.ScaleTraceLaw
import OAI.Probability.SLE.Geometry.RandomRestartEvents

namespace OAI

/-! Scaling the fresh Brownian driver by a scale chosen from the stopped
past preserves its exact restricted path law. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance restartScaleDriverRealMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance restartScaleDriverRealBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

def scaleDriverPath (c : ℝ≥0) (p : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) :=
  ⟨fun t => (c : ℝ) * p (sourceScaleTime c t),
    continuous_const.mul (p.continuous.comp (continuous_id.div_const (c ^ 2)))⟩

lemma measurable_scaleDriverPath :
    Measurable (fun x : ℝ≥0 × C(ℝ≥0, ℝ) => scaleDriverPath x.1 x.2) := by
  apply source_path_measurable
  intro t
  change Measurable (fun x : ℝ≥0 × C(ℝ≥0, ℝ) =>
    (x.1 : ℝ) * x.2 (t / x.1 ^ 2))
  exact NNReal.continuous_coe.measurable.comp measurable_fst |>.mul
    (continuous_eval.measurable.comp
      (measurable_snd.prodMk (measurable_const.div (measurable_fst.pow_const 2))))

lemma brownian_scaled_driver_path_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (c : ℝ≥0) (hcpos : 0 < c) :
    (P.map (sourceDriverPath B hc)).map (scaleDriverPath c) =
      P.map (sourceDriverPath B hc) := by
  let Bc : ℝ≥0 → Ω → ℝ := fun t ω => (c : ℝ) * B (sourceScaleTime c t) ω
  have hBc : IsBrownianReal Bc P := by
    have hh := hB.smul (c := (c ^ 2)⁻¹) (inv_ne_zero (pow_ne_zero 2 hcpos.ne'))
    simpa only [Bc, sourceScaleTime, NNReal.coe_inv, NNReal.coe_pow, Real.sqrt_inv,
      Real.sqrt_sq c.coe_nonneg, inv_inv, div_eq_mul_inv, mul_comm] using hh
  have hmc : ∀ t, Measurable (Bc t) := fun t => measurable_const.mul (hm _)
  have hcc : ∀ ω, Continuous (fun t => Bc t ω) := fun ω =>
    continuous_const.mul ((hc ω).comp (continuous_id.div_const (c ^ 2)))
  have hs : Measurable (scaleDriverPath c) :=
    measurable_scaleDriverPath.comp measurable_prodMk_left
  rw [Measure.map_map hs (source_path_measurable _ hm)]
  exact (ScaleTraceLaw.brownian_continuous_path_law B Bc hB hBc hm hmc hc hcc).symm

/-- A measurable transformation of the fresh path may depend on the stopped
past if each of its sections preserves the fresh path law. -/
theorem restart_random_transform_law
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure X) [IsFiniteMeasure ν]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → X) (hY : Measurable[mΩ] Y)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A →
      @Measure.map Ω X mΩ mX Y (P.restrict A) = P A • ν)
    (H : Ω × X → X) (hH : @Measurable (Ω × X) X (m.prod mX) mX H)
    (hsections : ∀ ω, ν.map (fun x => H (ω, x)) = ν)
    (A : Set Ω) (hA : MeasurableSet[m] A) :
    @Measure.map Ω X mΩ mX (fun ω => H (ω, Y ω)) (P.restrict A) = P A • ν := by
  let : MeasurableSpace Ω := mΩ
  have hj : @Measurable Ω (Ω × X) mΩ (m.prod mX) (fun ω => (ω, Y ω)) :=
    (measurable_id'' hm).prodMk hY
  apply Measure.ext
  intro D hD
  let E : Set (Ω × X) := H ⁻¹' D
  have hE : @MeasurableSet (Ω × X) (m.prod mX) E := hH hD
  let f : Ω × X → ℝ≥0∞ := (A ×ˢ univ).indicator (E.indicator (fun _ => 1))
  have hf : @Measurable (Ω × X) ℝ≥0∞ (m.prod mX) _ f :=
    (measurable_const.indicator hE).indicator (hA.prod MeasurableSet.univ)
  have he := @restart_lintegral_random_test Ω X mΩ mX P inferInstance ν inferInstance
    m hm Y hY hlaw f hf
  have hsec (ω : Ω) : (∫⁻ x, f (ω, x) ∂ν) = A.indicator (fun _ => ν D) ω := by
    by_cases hω : ω ∈ A
    · have hHx : Measurable (fun x => H (ω, x)) := hH.comp measurable_prodMk_left
      have hfun : (fun x => f (ω, x)) =
          ((fun x => H (ω, x)) ⁻¹' D).indicator (fun _ => 1) := by
        funext x
        by_cases hd : H (ω, x) ∈ D <;> simp [f, E, hω, hd]
      rw [hfun, lintegral_indicator (hHx hD), setLIntegral_const, one_mul,
        ← Measure.map_apply hHx hD, hsections ω, indicator_of_mem hω]
    · simp [f, hω]
  have hfun : (fun ω => f (ω, Y ω)) =
      A.indicator ((fun ω => H (ω, Y ω)) ⁻¹' D |>.indicator (fun _ => 1)) := by
    funext ω
    by_cases hω : ω ∈ A <;> by_cases hd : H (ω, Y ω) ∈ D <;> simp [f, E, hω, hd]
  rw [hfun] at he
  simp_rw [hsec] at he
  rw [lintegral_indicator (hm A hA),
    lintegral_indicator (hm A hA), setLIntegral_const] at he
  have hscaled : Measurable (fun ω => H (ω, Y ω)) := hH.comp hj
  rw [Measure.map_apply hscaled hD, Measure.restrict_apply (hscaled hD),
    Measure.smul_apply, smul_eq_mul]
  rw [setLIntegral_indicator (hscaled hD), setLIntegral_const, one_mul] at he
  simpa only [mul_comm] using he

/-- The normalized fresh driver has the original continuous Brownian law
on every event in the stopped past, even with a random past-measurable scale. -/
theorem source_restart_random_scale_driver_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (c : Ω → ℝ≥0) (hcm : Measurable[hτ.measurableSpace] c) (hcpos : ∀ ω, 0 < c ω)
    (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A) :
    (P.restrict A).map (fun ω => scaleDriverPath (c ω) (sourceRestartDriverPath B hc τ ω)) =
      P A • P.map (sourceDriverPath B hc) := by
  have hrm : Measurable (sourceRestartDriverPath B hc τ) :=
    source_path_measurable _ (fun t => (measurable_pi_apply t).comp
      (brownianRestart_measurable hm hc (stopping_time_measurable_nnreal hτ)))
  let ν := P.map (sourceDriverPath B hc)
  have : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff (source_path_measurable _ hm).aemeasurable).mpr inferInstance
  apply restart_random_transform_law P ν hτ.measurableSpace hτ.measurableSpace_le
    (sourceRestartDriverPath B hc τ) hrm
    (fun A hA => source_restart_continuous_driver_law hB hm hc τ hτ hA)
    (fun p => scaleDriverPath (c p.1) p.2)
    (measurable_scaleDriverPath.comp ((hcm.comp measurable_fst).prodMk measurable_snd))
    (fun ω => brownian_scaled_driver_path_law P B hB hm hc (c ω) (hcpos ω)) A hA

end SLEExactGauge

end

end OAI
