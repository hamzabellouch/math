import OAI.Probability.SLE.Loewner.StoppedDriverConcatenation
import OAI.Probability.SLE.Geometry.RandomRestartEvents

namespace OAI

/-! Conditional path tests after a finite restart. Splitting again at τ+t
identifies the conditional mean in the full original stopped filtration;
no factorization of its events through the restarted path is required. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance continuationDriverMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance continuationDriverBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

def driverContinuationMean (ν : Measure C(ℝ≥0,ℝ)) (t : ℝ≥0)
    (f : C(ℝ≥0,ℝ) → ℝ≥0∞) (p : C(ℝ≥0,ℝ)) : ℝ≥0∞ :=
  ∫⁻ q, f (concatenateDriverPath t (driverPathStopped t p) q) ∂ν

lemma driverContinuation_test_measurable (t : ℝ≥0)
    (f : C(ℝ≥0,ℝ) → ℝ≥0∞) (hf : Measurable f) :
    Measurable[(driverPathFiltration t).prod (borel C(ℝ≥0,ℝ))]
      (fun x : C(ℝ≥0,ℝ) × C(ℝ≥0,ℝ) =>
        f (concatenateDriverPath t (driverPathStopped t x.1) x.2)) := by
  exact hf.comp (measurable_concatenateDriverPath.comp
    (measurable_const.prodMk (((driverPathStopped_measurable_past t).comp measurable_fst).prodMk
      measurable_snd)))

lemma driverContinuationMean_measurable (ν : Measure C(ℝ≥0,ℝ)) [SFinite ν]
    (t : ℝ≥0) (f : C(ℝ≥0,ℝ) → ℝ≥0∞) (hf : Measurable f) :
    Measurable[driverPathFiltration t] (driverContinuationMean ν t f) :=
  @Measurable.lintegral_prod_right' _ _ (driverPathFiltration t) (borel _) ν _ _
    (driverContinuation_test_measurable t f hf)

lemma sourceRestartDriverPath_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Measurable (sourceRestartDriverPath B hc τ) :=
  source_path_measurable _ (fun t => (measurable_pi_apply t).comp
    (brownianRestart_measurable hm hc (stopping_time_measurable_nnreal hτ)))

theorem source_driver_continuation_condLExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (t : ℝ≥0) (f : C(ℝ≥0,ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (fun ω => driverContinuationMean (P.map (sourceDriverPath B hc)) t f
      (sourceDriverPath B hc ω)) =ᵐ[P]
    P⁻[(fun ω => f (sourceDriverPath B hc ω)) |
      (Filtration.natural B (fun s => (hm s).stronglyMeasurable)) t] := by
  let ℱ := Filtration.natural B (fun s => (hm s).stronglyMeasurable)
  have hσ := isStoppingTime_const ℱ t
  have hp : Measurable (sourceDriverPath B hc) := source_path_measurable _ hm
  let ν := P.map (sourceDriverPath B hc)
  let : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  have hZ : Measurable[hσ.measurableSpace]
      (fun ω => driverPathStopped t (sourceDriverPath B hc ω)) :=
    source_stoppedDriverPath_measurable B hm hc (fun _ => t) hσ
  have htest : Measurable[hσ.measurableSpace.prod (borel C(ℝ≥0,ℝ))]
      (fun x : Ω × C(ℝ≥0,ℝ) =>
        f (concatenateDriverPath t (driverPathStopped t (sourceDriverPath B hc x.1)) x.2)) :=
    hf.comp (measurable_concatenateDriverPath.comp
      (measurable_const.prodMk ((hZ.comp measurable_fst).prodMk measurable_snd)))
  have h := restart_condLExp_random_test P ν hσ.measurableSpace hσ.measurableSpace_le
    (sourceRestartDriverPath B hc (fun _ => t))
    (sourceRestartDriverPath_measurable B hm hc _ hσ)
    (fun A hA => source_restart_continuous_driver_law hB hm hc _ hσ hA) _ htest
  have he (ω : Ω) : concatenateDriverPath t
      (driverPathStopped t (sourceDriverPath B hc ω))
      (sourceRestartDriverPath B hc (fun _ => t) ω)=sourceDriverPath B hc ω :=
    concatenate_stopped_restart _ _
  simpa only [driverContinuationMean,he,IsStoppingTime.measurableSpace_const] using h

/-- Deterministic-time conditional identities identify the continuation
section on the canonical driver law. -/
theorem driverContinuationMean_eq_of_past_integrals
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (t : ℝ≥0) (f K : C(ℝ≥0,ℝ) → ℝ≥0∞) (hf : Measurable f)
    (hK : Measurable[driverPathFiltration t] K)
    (hmean : ∀ A : Set Ω,
      MeasurableSet[(Filtration.natural B (fun s => (hm s).stronglyMeasurable)) t] A →
      (∫⁻ ω in A, f (sourceDriverPath B hc ω) ∂P)=
        ∫⁻ ω in A, K (sourceDriverPath B hc ω) ∂P) :
    driverContinuationMean (P.map (sourceDriverPath B hc)) t f =ᵐ[P.map (sourceDriverPath B hc)] K := by
  let ℱ := Filtration.natural B (fun s => (hm s).stronglyMeasurable)
  have hp : Measurable (sourceDriverPath B hc) := source_path_measurable _ hm
  let : IsProbabilityMeasure (P.map (sourceDriverPath B hc)) :=
    (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  have hBP : Measurable[ℱ t,driverPathFiltration t] (sourceDriverPath B hc) :=
    driverPath_measurable_past_of_adapted ℱ _
      (fun s => (Filtration.stronglyAdapted_natural (fun s => (hm s).stronglyMeasurable) s).measurable) t
  have hk := ae_eq_condLExp (ℱ.le t) P (fun ω => f (sourceDriverPath B hc ω))
    (hK.comp hBP) (fun A hA => (hmean A hA).symm)
  have he := (source_driver_continuation_condLExp hB hm hc t f hf).trans hk.symm
  exact (ae_map_iff hp.aemeasurable (measurableSet_eq_fun
    ((driverContinuationMean_measurable _ t f hf).mono (driverPathFiltration.le t) le_rfl)
    (hK.mono (driverPathFiltration.le t) le_rfl))).mpr he

/-- The conditioning sigma algebra is the full original past at τ+t. -/
theorem source_restart_continuation_condLExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun s => (hm s).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (t : ℝ≥0) (f : C(ℝ≥0,ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (fun ω => driverContinuationMean (P.map (sourceDriverPath B hc)) t f
      (sourceRestartDriverPath B hc τ ω)) =ᵐ[P]
    P⁻[(fun ω => f (sourceRestartDriverPath B hc τ ω)) | shiftedStoppingFiltration hτ t] := by
  let σ := fun ω => τ ω+t
  have hσ := stopping_time_add_nnreal hτ t
  have hp : Measurable (sourceDriverPath B hc) := source_path_measurable _ hm
  let ν := P.map (sourceDriverPath B hc)
  let : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  have hY := driverPath_measurable_past_of_adapted (shiftedStoppingFiltration hτ)
    (sourceRestartDriverPath B hc τ) (sourceRestartDriverPath_shifted_adapted B hm hc τ hτ) t
  have hZ : Measurable[hσ.measurableSpace]
      (fun ω => driverPathStopped t (sourceRestartDriverPath B hc τ ω)) :=
    (driverPathStopped_measurable_past t).comp hY
  have htest : Measurable[hσ.measurableSpace.prod (borel C(ℝ≥0,ℝ))]
      (fun x : Ω × C(ℝ≥0,ℝ) =>
        f (concatenateDriverPath t (driverPathStopped t (sourceRestartDriverPath B hc τ x.1)) x.2)) :=
    hf.comp (measurable_concatenateDriverPath.comp
      (measurable_const.prodMk ((hZ.comp measurable_fst).prodMk measurable_snd)))
  have h := restart_condLExp_random_test P ν hσ.measurableSpace hσ.measurableSpace_le
    (sourceRestartDriverPath B hc σ) (sourceRestartDriverPath_measurable B hm hc σ hσ)
    (fun A hA => source_restart_continuous_driver_law hB hm hc σ hσ hA) _ htest
  have he (ω : Ω) : concatenateDriverPath t
      (driverPathStopped t (sourceRestartDriverPath B hc τ ω))
      (sourceRestartDriverPath B hc σ ω)=sourceRestartDriverPath B hc τ ω :=
    (sourceRestartDriverPath_split B hc τ t ω).symm
  simpa only [driverContinuationMean,he,shiftedStoppingFiltration,σ,ν] using h

/-- A canonical section identity therefore holds in the larger shifted
filtration, not merely in the natural filtration of the fresh driver. -/
theorem source_restart_condLExp_of_section_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun s => (hm s).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (t : ℝ≥0) (f K : C(ℝ≥0,ℝ) → ℝ≥0∞) (hf : Measurable f) (hK : Measurable K)
    (hsection : driverContinuationMean (P.map (sourceDriverPath B hc)) t f
      =ᵐ[P.map (sourceDriverPath B hc)] K) :
    (fun ω => K (sourceRestartDriverPath B hc τ ω)) =ᵐ[P]
    P⁻[(fun ω => f (sourceRestartDriverPath B hc τ ω)) | shiftedStoppingFiltration hτ t] := by
  have hp : Measurable (sourceDriverPath B hc) := source_path_measurable _ hm
  let : IsProbabilityMeasure (P.map (sourceDriverPath B hc)) :=
    (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  have hfull := sourceRestart_mem_full_driver_set hB hm hc τ hτ _
    (measurableSet_eq_fun
      ((driverContinuationMean_measurable _ t f hf).mono (driverPathFiltration.le t) le_rfl) hK) hsection
  have he : (fun ω => driverContinuationMean (P.map (sourceDriverPath B hc)) t f
      (sourceRestartDriverPath B hc τ ω)) =ᵐ[P]
      (fun ω => K (sourceRestartDriverPath B hc τ ω)) := hfull
  exact he.symm.trans (source_restart_continuation_condLExp hB hm hc τ hτ t f hf)


theorem source_restart_integral_of_section_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun s => (hm s).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (t : ℝ≥0) (f K : C(ℝ≥0,ℝ) → ℝ≥0∞) (hf : Measurable f) (hK : Measurable K)
    (hsection : driverContinuationMean (P.map (sourceDriverPath B hc)) t f
      =ᵐ[P.map (sourceDriverPath B hc)] K)
    (E : Set Ω) (hE : MeasurableSet[shiftedStoppingFiltration hτ t] E) :
    (∫⁻ ω in E, f (sourceRestartDriverPath B hc τ ω) ∂P)=
      ∫⁻ ω in E, K (sourceRestartDriverPath B hc τ ω) ∂P := by
  have he := source_restart_condLExp_of_section_ae hB hm hc τ hτ t f K hf hK hsection
  calc
    _ = ∫⁻ ω in E,
        P⁻[(fun ω => f (sourceRestartDriverPath B hc τ ω)) | shiftedStoppingFiltration hτ t] ω ∂P :=
      (setLIntegral_condLExp ((shiftedStoppingFiltration hτ).le t) P _ hE).symm
    _ = _ := lintegral_congr_ae (ae_restrict_of_ae he.symm)


theorem source_restart_integral_of_original_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (t : ℝ≥0) (f K : C(ℝ≥0,ℝ) → ℝ≥0∞) (hf : Measurable f)
    (hK : Measurable[driverPathFiltration t] K)
    (hmean : ∀ A : Set Ω,
      MeasurableSet[(Filtration.natural B (fun s => (hm s).stronglyMeasurable)) t] A →
      (∫⁻ ω in A, f (sourceDriverPath B hc ω) ∂P)=
        ∫⁻ ω in A, K (sourceDriverPath B hc ω) ∂P)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun s => (hm s).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (E : Set Ω) (hE : MeasurableSet[shiftedStoppingFiltration hτ t] E) :
    (∫⁻ ω in E, f (sourceRestartDriverPath B hc τ ω) ∂P)=
      ∫⁻ ω in E, K (sourceRestartDriverPath B hc τ ω) ∂P :=
  source_restart_integral_of_section_ae hB hm hc τ hτ t f K hf
    (hK.mono (driverPathFiltration.le t) le_rfl)
    (driverContinuationMean_eq_of_past_integrals hB hm hc t f K hf hK hmean) E hE


/-- Measure-kernel form of the continuation identity. This applies to the
sum of the finite-time raw mass and its current Green measure. -/
theorem source_restart_bind_of_original_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (t : ℝ≥0) (N K : C(ℝ≥0,ℝ) → Measure upperHalfPlane) (hN : Measurable N)
    (hK : Measurable[driverPathFiltration t] K)
    (hmean : ∀ A : Set Ω,
      MeasurableSet[(Filtration.natural B (fun s => (hm s).stronglyMeasurable)) t] A →
      (P.restrict A).bind (fun ω => N (sourceDriverPath B hc ω))=
        (P.restrict A).bind (fun ω => K (sourceDriverPath B hc ω)))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun s => (hm s).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (E : Set Ω) (hE : MeasurableSet[shiftedStoppingFiltration hτ t] E) :
    (P.restrict E).bind (fun ω => N (sourceRestartDriverPath B hc τ ω))=
      (P.restrict E).bind (fun ω => K (sourceRestartDriverPath B hc τ ω)) := by
  have hp : Measurable (sourceDriverPath B hc) := source_path_measurable _ hm
  have hY := sourceRestartDriverPath_measurable B hm hc τ hτ
  have hKm := hK.mono (driverPathFiltration.le t) le_rfl
  have hNY : Measurable (fun ω => N (sourceRestartDriverPath B hc τ ω)) := hN.comp hY
  have hKY : Measurable (fun ω => K (sourceRestartDriverPath B hc τ ω)) := hKm.comp hY
  have hNB : Measurable (fun ω => N (sourceDriverPath B hc ω)) := hN.comp hp
  have hKB : Measurable (fun ω => K (sourceDriverPath B hc ω)) := hKm.comp hp
  apply Measure.ext
  intro S hS
  rw [Measure.bind_apply hS hNY.aemeasurable,
    Measure.bind_apply hS hKY.aemeasurable]
  apply source_restart_integral_of_original_kernel hB hm hc t
    (fun p => N p S) (fun p => K p S)
    ((Measure.measurable_coe hS).comp hN) ((Measure.measurable_coe hS).comp hK) ?_ τ hτ E hE
  intro A hA
  have he := congrArg (fun μ : Measure upperHalfPlane => μ S) (hmean A hA)
  simpa only [Measure.bind_apply hS hNB.aemeasurable,
    Measure.bind_apply hS hKB.aemeasurable] using he

end SLEExactGauge

end

end OAI
