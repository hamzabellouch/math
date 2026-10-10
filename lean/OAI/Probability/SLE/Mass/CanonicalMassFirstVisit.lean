import OAI.Probability.SLE.Mass.CanonicalMassRemaining

namespace OAI

/-! At each fixed time the canonical mass is the terminal measure
restricted to the already visited trace. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

lemma halfPlaneStoppingGreenMeasure_const
    {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ) (t : ℝ≥0) :
    halfPlaneStoppingGreenMeasure κ B γ G (fun _ => (t:ℝ≥0∞)) =
      halfPlaneGreenMeasure κ B γ G t := by
  funext ω
  simp only [halfPlaneStoppingGreenMeasure,stoppingGreen,ENNReal.coe_lt_top,
    ite_true,ENNReal.toNNReal_coe,halfPlaneGreenMeasure]

theorem CanonicalMass.atTime_eq_restrict_past
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (C : CanonicalMass P κ B hBm γ G) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, C.atTime t ω = (C.rational.terminal ω).restrict
      {z : upperHalfPlane | (z:ℂ) ∈ γ ω '' Icc 0 t} := by
  let ℱ := Filtration.natural B (fun r =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)
  have hstop : IsStoppingTime ℱ (fun _ => (t:WithTop ℝ≥0)) := isStoppingTime_const ℱ t
  obtain ⟨η,hηm,hηr,hηsum,hηkernel⟩ := C.exists_remaining_kernel _ hstop
  have hevent (E : Set Ω) (hE : MeasurableSet[ℱ t] E) :
      (P.restrict E).bind η = (P.restrict E).bind (halfPlaneGreenMeasure κ B γ G t) := by
    rw [← halfPlaneStoppingGreenMeasure_const κ B γ G t]
    apply hηkernel E
    change MeasurableSet[(isStoppingTime_const ℱ t).measurableSpace] E
    rw [IsStoppingTime.measurableSpace_const]
    exact hE
  have hfuture := ae_remainder_carried_by_surviving hB hBm hBc hB0 hκ hκ8 γ G F hw
    t η hηm (fun ω => (hηr ω).2) hevent
  have hlim := C.rational.all_finite_times_limit hBc hκ hκ8 F hw C.process C.radon C.paths
  filter_upwards [hηsum,hfuture,hlim] with ω hsum hfuture hlim
  let A : Set upperHalfPlane := {z | (z:ℂ) ∈ γ ω '' Icc 0 t}
  have hA : MeasurableSet A :=
    ((isCompact_Icc.image (hw ω).1).isClosed.preimage continuous_subtype_val).measurableSet
  let : (C.atTime t ω).Regular := (C.atTime_radon t ω).1
  have hpast : C.atTime t ω Aᶜ = 0 := by
    have hh := convex_level_radon_limit_carried_by_past ω (hBc ω) (hw ω) t (fun n => (n:ℝ))
      tendsto_natCast_atTop_atTop C.rational.supports C.rational.weights
      (C.atTime t ω) (by
        simpa only [CanonicalMass.atTime,extendedCanonicalMass,ENNReal.coe_lt_top,
          ite_true,ENNReal.toNNReal_coe] using hlim t)
    exact hh
  have hηA : η ω A = 0 := by
    apply le_zero_iff.mp
    apply (measure_mono (show A ⊆ {z : upperHalfPlane | (z:ℂ) ∉ survivingDomain (γ ω) t} from ?_)).trans_eq hfuture
    intro z hz hs
    exact hs.1.2 hz
  have hrestr : (C.atTime t ω).restrict A = C.atTime t ω := by
    apply Measure.restrict_eq_self_of_ae_mem
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hpast] with z hz
    exact not_not.mp hz
  change C.atTime t ω = (C.rational.terminal ω).restrict A
  rw [← hsum,Measure.restrict_add,Measure.restrict_eq_zero.mpr hηA,zero_add]
  exact hrestr.symm

end SLEExactGauge.Multipoint

end

end OAI
