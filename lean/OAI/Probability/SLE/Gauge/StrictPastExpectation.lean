import OAI.Probability.SLE.Geometry.FirstSuccessfulPast

namespace OAI

/-! The finite past-mass identity before exhaustion over rational times. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
attribute [local instance] Classical.propDecidable

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G) (hB : IsBrownianReal B P)
  (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
  (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))

include C hB hc h0 hκ hκ8 F hw

lemma strict_past_mass_aemeasurable (t : ℝ≥0) (K : Set upperHalfPlane) (hK : IsCompact K) :
    AEMeasurable (fun ω => C.rational.terminal ω
      (K \ {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 t})) P := by
  have hNm : Measurable (C.process t) := by
    simpa only [atTime,extendedCanonicalMass,ENNReal.coe_lt_top,ite_true,ENNReal.toNNReal_coe]
      using C.atTime_measurable (fun _ => (t:ℝ≥0∞)) measurable_const
  have hm : Measurable (fun ω => C.rational.terminal ω K-C.process t ω K) :=
    ((Measure.measurable_coe hK.measurableSet).comp C.rational.terminal_measurable).sub
      ((Measure.measurable_coe hK.measurableSet).comp hNm)
  apply hm.aemeasurable.congr
  have hp : ∀ᵐ ω ∂P, C.process t ω=(C.rational.terminal ω).restrict
      {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 t} := by
    simpa only [atTime,extendedCanonicalMass,ENNReal.coe_lt_top,ite_true,ENNReal.toNNReal_coe]
      using C.atTime_eq_restrict_past hB hBm hc h0 hκ hκ8 F hw t
  filter_upwards [hp] with ω hω
  have hsum : C.process t ω K+C.rational.terminal ω
      (K \ {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 t})=C.rational.terminal ω K := by
    rw [hω,Measure.restrict_apply hK.measurableSet]
    exact measure_inter_add_sdiff K
      (((isCompact_Icc.image (hw ω).1).isClosed.preimage continuous_subtype_val).measurableSet)
  let := (C.radon t ω).2
  rw [← hsum,ENNReal.add_sub_cancel_left hK.measure_lt_top.ne]

lemma finite_strict_past_expectation (I : Finset ℝ≥0) (E : ℝ≥0 → Set Ω)
    (hE : ∀ t∈I, MeasurableSet[(Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) t] (E t))
    (K : Set upperHalfPlane) (hK : IsCompact K) :
    (∫⁻ ω, C.rational.terminal ω (K ∩ ⋃ t∈I,
      if ω∈E t then {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 t}ᶜ else ∅) ∂P)=
      ∑ t∈I, ∫⁻ ω in firstPastSuccess I E t, halfPlaneGreenMeasure κ B γ G t ω K ∂P := by
  let ℱ := Filtration.natural B (fun s =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)
  let f (t : ℝ≥0) := (firstPastSuccess I E t).indicator (fun ω => C.rational.terminal ω
    (K \ {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 t}))
  have hfirst (t) (ht : t∈I) : MeasurableSet (firstPastSuccess I E t) :=
    (ℱ.le t) _ (firstPastSuccess_measurable ℱ I E hE ht)
  have hf (t) (ht : t∈I) : AEMeasurable (f t) P :=
    (C.strict_past_mass_aemeasurable hB hc h0 hκ hκ8 F hw t K hK).indicator (hfirst t ht)
  calc
    _ = ∫⁻ ω, ∑ t∈I, f t ω ∂P := by
      apply lintegral_congr
      intro ω
      simpa only [f,Set.indicator,mem_ofPred_eq] using firstPastSuccess_future_mass
        (C.rational.terminal ω) K I E
        (fun t => {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 t})
        (fun s t hst z hz => by
          obtain ⟨r,hr,he⟩ := hz
          exact ⟨r,⟨hr.1,hr.2.trans hst⟩,he⟩) ω
    _ = ∑ t∈I, ∫⁻ ω, f t ω ∂P := lintegral_finsetSum' I hf
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [show f t=(firstPastSuccess I E t).indicator (fun ω => C.rational.terminal ω
        (K \ {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 t})) from rfl,
        lintegral_indicator (hfirst t ht)]
      exact C.strict_past_mass_kernel hB hc h0 hκ hκ8 F hw t _
        (firstPastSuccess_measurable ℱ I E hE ht) K hK

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
