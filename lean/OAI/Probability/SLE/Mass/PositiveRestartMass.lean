import OAI.Probability.SLE.Mass.CanonicalMassRestart
import OAI.Probability.SLE.Geometry.RestartGreenKernel

namespace OAI

/-! Positive mass survives the actual inverse-Loewner transport and
passes from initial intervals to every finite Brownian restart. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace SLEExactGauge

lemma weightedImageMass_ne_zero {X : Type*} [MeasurableSpace X]
    (J : upperHalfPlane → X) (hJ : Measurable J)
    (w : upperHalfPlane → ℝ≥0∞) (hw : Measurable w) (hp : ∀ z, 0<w z)
    (μ : Measure upperHalfPlane) (hμ : μ≠0) : weightedImageMass J w μ≠0 := by
  apply Measure.measure_univ_pos.mp
  rw [weightedImageMass_apply J hJ w μ univ MeasurableSet.univ]
  simp only [preimage_univ,indicator_univ]
  rw [lintegral_pos_iff_support hw]
  have he : Function.support w=univ := by
    ext z
    simp only [Function.mem_support,mem_univ,iff_true]
    exact (hp z).ne'
  rw [he]
  exact Measure.measure_univ_pos.mpr hμ

namespace Multipoint.CanonicalMass

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

local instance positiveRestartDriverMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance positiveRestartDriverBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

lemma raw_restart_positive_time
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (R : RawCanonicalMass)
    (he : ∀ᵐ ω ∂P, ∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω)
    (hpos : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0<t → C.process t ω≠0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable))
      (fun ω => (τ ω:WithTop ℝ≥0)))
    (t : ℝ≥0) (ht : 0<t) :
    ∀ᵐ ω ∂P, R.process t (sourceRestartDriverPath B hc τ ω)≠0 := by
  let E : Set C(ℝ≥0,ℝ) := {p | 0<R.process t p univ}
  have hEm : MeasurableSet E := measurableSet_lt measurable_const
    ((Measure.measurable_coe MeasurableSet.univ).comp (R.progressive.adapted.measurable (i:=t)))
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  have hp := source_path_measurable (sourceDriverPath B hc) hm
  have hEfull : ∀ᵐ p ∂P.map (sourceDriverPath B hc), p∈E := by
    apply (ae_map_iff hp.aemeasurable hEm).mpr
    filter_upwards [he,hpos] with ω hω hωp
    rw [hω t]
    exact Measure.measure_univ_pos.mpr (hωp t ht)
  filter_upwards [sourceRestart_mem_full_driver_set hB hm hc τ hτ E hEm hEfull] with ω hω
  exact Measure.measure_univ_pos.mp hω

lemma positive_increment_after_stop
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0<κ)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (hpos : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0<t → C.process t ω≠0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable))
      (fun ω => (τ ω:WithTop ℝ≥0)))
    (t : ℝ≥0) (ht : 0<t) :
    ∀ᵐ ω ∂P, C.process (τ ω+t) ω-C.process (τ ω) ω≠0 := by
  obtain ⟨R,he,hr⟩ := C.exists_raw_pathwise_restart hB hc hκ F hw hpublished
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  have hJ := stoppedMassPoint_measurable B κ γ G F hw τ hm hc hτ
  have hW := stoppedMassWeight_measurable B κ γ G F hw τ hm hc hτ hκ
  have hpair (ω : Ω) : @Measurable upperHalfPlane (Ω × upperHalfPlane) inferInstance
      (hτ.measurableSpace.prod inferInstance) (fun z => (ω,z)) :=
    @measurable_prodMk_left Ω upperHalfPlane hτ.measurableSpace inferInstance ω
  have hJsec (ω : Ω) : Measurable (stoppedMassPoint B κ γ G F hw τ ω) :=
    @Measurable.comp upperHalfPlane (Ω × upperHalfPlane) upperHalfPlane
      inferInstance (hτ.measurableSpace.prod inferInstance) inferInstance
      (fun p => stoppedMassPoint B κ γ G F hw τ p.1 p.2) (fun z => (ω,z)) hJ (hpair ω)
  have hWsec (ω : Ω) : Measurable (stoppedMassWeight B κ F τ ω) :=
    @Measurable.comp upperHalfPlane (Ω × upperHalfPlane) ℝ≥0∞
      inferInstance (hτ.measurableSpace.prod inferInstance) inferInstance
      (fun p => stoppedMassWeight B κ F τ p.1 p.2) (fun z => (ω,z)) hW (hpair ω)
  filter_upwards [hr τ hτ,C.raw_restart_positive_time hB hc R (he.mono fun _ h => h.1)
    hpos τ hτ t ht,fresh_capacity_witness_exists hB hm hc hpublished τ hτ] with ω hω hp hf
  rw [hω.1 t]
  obtain ⟨β,G',F',hf⟩ := hf
  apply weightedImageMass_ne_zero (stoppedMassPoint B κ γ G F hw τ ω)
    (hJsec ω)
    (stoppedMassWeight B κ F τ ω)
    (hWsec ω)
    (fun z => ?_) _ hp
  exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos
    ((hw ω).restart_inverse_derivative_norm_pos ((hc ω).const_mul _) (τ ω) hf z z.property) _)

lemma positive_increment_fixed_times
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (hpos : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → C.process t ω ≠ 0)
    (s t : ℝ≥0) (hst : s < t) :
    ∀ᵐ ω ∂P, C.process t ω-C.process s ω ≠ 0 := by
  have hτ := isStoppingTime_const (Filtration.natural B (fun r =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)) s
  have h := C.positive_increment_after_stop hB hc hκ F hw hpublished hpos
    (fun _ => s) hτ (t-s) (tsub_pos_iff_lt.mpr hst)
  simpa only [add_tsub_cancel_of_le hst.le] using h

lemma positive_increment_all_times
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (hpos : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → C.process t ω ≠ 0) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s < t → C.process t ω-C.process s ω ≠ 0 := by
  have hq (p q : ℚ) : ∀ᵐ ω ∂P,
      (p:ℝ).toNNReal < (q:ℝ).toNNReal →
        C.process (q:ℝ).toNNReal ω-C.process (p:ℝ).toNNReal ω ≠ 0 := by
    by_cases hpq : (p:ℝ).toNNReal < (q:ℝ).toNNReal
    · exact (C.positive_increment_fixed_times hB hc hκ F hw hpublished hpos _ _ hpq).mono
        (fun _ h _ => h)
    · exact ae_of_all _ (fun _ h => (hpq h).elim)
  filter_upwards [C.paths,ae_all_iff.mpr (fun p => ae_all_iff.mpr (hq p))] with ω hp hqω
  intro s t hst hz
  obtain ⟨p,hsp,hpt⟩ := exists_rat_btwn (show (s:ℝ) < (t:ℝ) from hst)
  obtain ⟨q,hpq,hqt⟩ := exists_rat_btwn hpt
  have hp0 : (0:ℝ) ≤ p := s.coe_nonneg.trans hsp.le
  have hq0 : (0:ℝ) ≤ q := hp0.trans hpq.le
  have hsp' : s ≤ (p:ℝ).toNNReal := by
    exact_mod_cast (show (s:ℝ) ≤ ((p:ℝ).toNNReal:ℝ) by rw [Real.coe_toNNReal _ hp0]; exact hsp.le)
  have hpq' : (p:ℝ).toNNReal < (q:ℝ).toNNReal := by
    exact_mod_cast (show ((p:ℝ).toNNReal:ℝ) < ((q:ℝ).toNNReal:ℝ) by
      rw [Real.coe_toNNReal _ hp0,Real.coe_toNNReal _ hq0]; exact hpq)
  have hqt' : (q:ℝ).toNNReal ≤ t := by
    exact_mod_cast (show ((q:ℝ).toNNReal:ℝ) ≤ (t:ℝ) by rw [Real.coe_toNNReal _ hq0]; exact hqt.le)
  let : IsFiniteMeasureOnCompacts (C.process s ω) := (C.radon s ω).2
  have hts : C.process t ω=C.process s ω := by
    have h := sigmaFinite_sub_add_cancel_of_le (hp.monotone hst.le)
    rw [hz,zero_add] at h
    exact h.symm
  have hps : C.process (p:ℝ).toNNReal ω=C.process s ω := by
    apply le_antisymm
    · exact (hp.monotone (hpq'.le.trans hqt')).trans_eq hts
    · exact hp.monotone hsp'
  have hqs : C.process (q:ℝ).toNNReal ω=C.process s ω := by
    apply le_antisymm
    · exact (hp.monotone hqt').trans_eq hts
    · exact hp.monotone (hsp'.trans hpq'.le)
  apply hqω p q hpq'
  rw [hps,hqs,Measure.sub_self]

end Multipoint.CanonicalMass
end SLEExactGauge

end

end OAI
