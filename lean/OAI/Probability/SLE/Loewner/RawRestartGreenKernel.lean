import OAI.Probability.SLE.Geometry.CanonicalGreenPast
import OAI.Probability.SLE.Geometry.CanonicalRawTerminal
import OAI.Probability.SLE.Geometry.RestartContinuationKernel

namespace OAI

/-! The canonical mass's Green decomposition transfers to the full
original past at every time after a finite restart. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

local instance rawGreenKernelDriverMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance rawGreenKernelDriverBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

lemma bind_kernel_add {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (N M : Ω → Measure upperHalfPlane) (hN : Measurable N) (hM : Measurable M) :
    P.bind (fun ω => N ω+M ω)=P.bind N+P.bind M := by
  have hsum : Measurable (fun ω => N ω+M ω) := hN.add hM
  apply Measure.ext
  intro A hA
  rw [Measure.bind_apply hA hsum.aemeasurable,Measure.add_apply,
    Measure.bind_apply hA hN.aemeasurable,Measure.bind_apply hA hM.aemeasurable]
  simp only [Measure.add_apply]
  exact lintegral_add_left ((Measure.measurable_coe hA).comp hN) _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)
  (hc : ∀ ω, Continuous (fun t => B t ω))
  (F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
  (R : RawCanonicalMass)
  (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
    R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)

include C hc F hw R he in
lemma CanonicalMass.raw_green_kernel (t : ℝ≥0) (A : Set Ω)
    (hA : MeasurableSet[(Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) t] A) :
    (P.restrict A).bind (fun ω => R.terminal (sourceDriverPath B hc ω)) =
      (P.restrict A).bind (fun ω => R.process t (sourceDriverPath B hc ω)+
        canonicalGreenMass κ t (sourceDriverPath B hc ω)) := by
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  have hG (ω : Ω) : canonicalGreenMass κ t (sourceDriverPath B hc ω)=
      halfPlaneGreenMeasure κ B γ G t ω := by
    simpa only [sourceDriverPath,ContinuousMap.coe_mk,halfPlaneGreenMeasure] using
      canonicalGreenMass_eq κ (sourceDriverPath B hc ω) (hw ω) t
  have hleft : (P.restrict A).bind (fun ω => R.terminal (sourceDriverPath B hc ω)) =
      (P.restrict A).bind C.rational.terminal :=
    Measure.bind_congr_right (ae_restrict_of_ae (he.mono fun _ h => h.2))
  have hright : (P.restrict A).bind (fun ω => R.process t (sourceDriverPath B hc ω)+
        canonicalGreenMass κ t (sourceDriverPath B hc ω)) =
      (P.restrict A).bind (fun ω => C.process t ω+halfPlaneGreenMeasure κ B γ G t ω) := by
    apply Measure.bind_congr_right
    filter_upwards [ae_restrict_of_ae he] with ω hω
    rw [hω.1 t,hG ω]
  have hs := isStoppingTime_const (Filtration.natural B (fun s => (hm s).stronglyMeasurable)) t
  have hAs : MeasurableSet[hs.measurableSpace] A := by
    have hspace : hs.measurableSpace = (Filtration.natural B
        (fun s => (hm s).stronglyMeasurable)) t :=
      IsStoppingTime.measurableSpace_const _ t
    rw [hspace]
    exact hA
  have h := C.kernel (fun _ => (t:WithTop ℝ≥0)) hs A hAs
  change (P.restrict A).bind C.rational.terminal =
    (P.restrict A).bind (C.process t) +
      (P.restrict A).bind (halfPlaneGreenMeasure κ B γ G t) at h
  calc
    _ = (P.restrict A).bind C.rational.terminal := hleft
    _ = (P.restrict A).bind (C.process t) +
        (P.restrict A).bind (halfPlaneGreenMeasure κ B γ G t) := h
    _ = (P.restrict A).bind (fun ω => C.process t ω+halfPlaneGreenMeasure κ B γ G t ω) :=
      (bind_kernel_add _ _ _ (C.progressive.adapted.measurable (i := t))
        (halfPlaneGreenMeasure_measurable hBm hc κ γ G F hw t)).symm
    _ = _ := hright.symm

include C hc F hw R he in
theorem CanonicalMass.raw_restarted_green_kernel [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable))
      (fun ω => (τ ω:WithTop ℝ≥0)))
    (t : ℝ≥0) (E : Set Ω) (hE : MeasurableSet[shiftedStoppingFiltration hτ t] E) :
    (P.restrict E).bind (fun ω => R.terminal (sourceRestartDriverPath B hc τ ω)) =
      (P.restrict E).bind (fun ω => R.process t (sourceRestartDriverPath B hc τ ω))+
      (P.restrict E).bind (fun ω => canonicalGreenMass κ t (sourceRestartDriverPath B hc τ ω)) := by
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  have hK : Measurable[driverPathFiltration t]
      (fun p => R.process t p+canonicalGreenMass κ t p) :=
    (R.progressive.adapted t).add (canonicalGreenMass_measurable_past κ t)
  have h := source_restart_bind_of_original_kernel hB hm hc t R.terminal
    (fun p => R.process t p+canonicalGreenMass κ t p) R.terminal_measurable hK
    (fun A hA => C.raw_green_kernel hc F hw R he t A hA) τ hτ E hE
  rw [h]
  have hY := sourceRestartDriverPath_measurable B hm hc τ hτ
  exact bind_kernel_add _ _ _ ((R.progressive.adapted.measurable (i := t)).comp hY)
    ((canonicalGreenMass_measurable κ t).comp hY)

end SLEExactGauge.Multipoint

end

end OAI
