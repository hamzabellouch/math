import OAI.Probability.SLE.Mass.CanonicalMassFirstVisit

namespace OAI

/-! The expected terminal mass arriving strictly after a deterministic past
is its current Green mass, including arbitrary events in that past. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}

lemma strict_past_mass_kernel
    (C : CanonicalMass P κ B hBm γ G) (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0) (E : Set Ω)
    (hE : MeasurableSet[(Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) t] E)
    (K : Set upperHalfPlane) (hK : IsCompact K) :
    (∫⁻ ω in E, C.rational.terminal ω
      (K \ {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 t}) ∂P)=
      ∫⁻ ω in E, halfPlaneGreenMeasure κ B γ G t ω K ∂P := by
  let ℱ := Filtration.natural B (fun s =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)
  have hNm : Measurable (C.process t) := by
    simpa only [atTime,extendedCanonicalMass,ENNReal.coe_lt_top,ite_true,ENNReal.toNNReal_coe]
      using C.atTime_measurable (fun _ => (t:ℝ≥0∞)) measurable_const
  have hNG : Measurable (fun ω => C.process t ω K) :=
    (Measure.measurable_coe hK.measurableSet).comp hNm
  have hGm := halfPlaneGreenMeasure_measurable hBm hc κ γ G F hw t
  have hp : ∀ᵐ ω ∂P, C.process t ω=(C.rational.terminal ω).restrict
      {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 t} := by
    simpa only [atTime,extendedCanonicalMass,ENNReal.coe_lt_top,ite_true,ENNReal.toNNReal_coe]
      using C.atTime_eq_restrict_past hB hBm hc h0 hκ hκ8 F hw t
  have hdecomp : (∫⁻ ω in E, C.rational.terminal ω K ∂P)=
      (∫⁻ ω in E, C.process t ω K ∂P)+
      ∫⁻ ω in E, C.rational.terminal ω
        (K \ {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 t}) ∂P := by
    rw [← lintegral_add_left hNG]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae hp] with ω hω
    rw [hω,Measure.restrict_apply hK.measurableSet]
    exact (measure_inter_add_sdiff K
      (((isCompact_Icc.image (hw ω).1).isClosed.preimage continuous_subtype_val).measurableSet)).symm
  have hS : IsStoppingTime ℱ (fun _ : Ω => (t:WithTop ℝ≥0)) := isStoppingTime_const ℱ t
  have hEs : MeasurableSet[hS.measurableSpace] E := by
    change MeasurableSet[(isStoppingTime_const ℱ t).measurableSpace] E
    rw [IsStoppingTime.measurableSpace_const]
    exact hE
  have hk := congrArg (fun μ : Measure upperHalfPlane => μ K) (C.kernel _ hS E hEs)
  change ((P.restrict E).bind C.rational.terminal) K=
    (((P.restrict E).bind (C.process t))+((P.restrict E).bind (halfPlaneGreenMeasure κ B γ G t))) K at hk
  rw [Measure.add_apply,Measure.bind_apply hK.measurableSet C.rational.terminal_measurable.aemeasurable,
    Measure.bind_apply hK.measurableSet hNm.aemeasurable,
    Measure.bind_apply hK.measurableSet hGm.aemeasurable] at hk
  have hfin : (∫⁻ ω in E, C.process t ω K ∂P)≠∞ := by
    let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
    have hb := C.atTime_mean_le (fun _ => (t:ℝ≥0∞)) measurable_const E K
    change ((P.restrict E).bind (C.process t)) K ≤ initialGreenMeasure κ K at hb
    rw [Measure.bind_apply hK.measurableSet hNm.aemeasurable] at hb
    exact (hb.trans_lt hK.measure_lt_top).ne
  apply (ENNReal.add_right_inj hfin).mp
  simpa only [add_comm] using hdecomp.symm.trans hk

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
