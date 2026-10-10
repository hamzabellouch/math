import OAI.Probability.SLE.Mass.RawScaledMassPaths
import OAI.Probability.SLE.Mass.ScaledGreenMeasure
import OAI.Probability.SLE.Mass.GreenMassProcessUniqueness

namespace OAI

/-! Mean bounds and equal Green remainders for the physical dilation
and the canonical functional of the scaled Brownian driver. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint

local instance rawScaledMeansMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance rawScaledMeansBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

lemma bind_comp_eq_of_path_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : Ω → C(ℝ≥0,ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (hXY : P.map X=P.map Y) (N : C(ℝ≥0,ℝ) → Measure upperHalfPlane) (hN : Measurable N) :
    P.bind (fun ω => N (X ω))=P.bind (fun ω => N (Y ω)) := by
  calc
    _ = (P.map X).bind N := by
      unfold Measure.bind
      rw [Measure.map_map hN hX]
      rfl
    _ = (P.map Y).bind N := by rw [hXY]
    _ = _ := by
      unfold Measure.bind
      rw [Measure.map_map hN hY]
      rfl

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G) (hB : IsBrownianReal B P)
  (hc : ∀ ω, Continuous (fun t => B t ω))
  (R : RawCanonicalMass)
  (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
    R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
  (c : ℝ≥0) (hcp : 0 < c)

include C hB hc R he c hcp in
omit [IsProbabilityMeasure P] in
lemma CanonicalMass.scaledRawMass_mean_le (t : ℝ≥0) :
    P.bind (scaledRawMass R c B hc t) ≤ initialGreenMeasure κ := by
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  have hp := source_path_measurable (sourceDriverPath B hc) hm
  have hy := source_path_measurable
    (sourceDriverPath (scaledBrownianDriver c B) (scaledBrownianDriver_continuous c B hc))
    (scaledBrownianDriver_measurable c B hm)
  have h := bind_comp_eq_of_path_law P _ _ hy hp
    (scaledBrownianDriver_path_law c hcp B hB hm hc) (R.process (c^2*t))
    (R.progressive.adapted.measurable (i:=c^2*t))
  change P.bind (scaledRawMass R c B hc t)=_ at h
  rw [h,Measure.bind_congr_right (he.mono (fun _ h => h.1 (c^2*t)))]
  simpa only [Measure.restrict_univ] using C.uniqueness_process_mean_le (c^2*t) univ

include C hB hc R he c hcp in
omit [IsProbabilityMeasure P] in
lemma CanonicalMass.scaledRawTerminal_mean :
    P.bind (scaledRawTerminal R c B hc)=initialGreenMeasure κ := by
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  have hp := source_path_measurable (sourceDriverPath B hc) hm
  have hy := source_path_measurable
    (sourceDriverPath (scaledBrownianDriver c B) (scaledBrownianDriver_continuous c B hc))
    (scaledBrownianDriver_measurable c B hm)
  have h := bind_comp_eq_of_path_law P _ _ hy hp
    (scaledBrownianDriver_path_law c hcp B hB hm hc) R.terminal R.terminal_measurable
  change P.bind (scaledRawTerminal R c B hc)=_ at h
  rw [h,Measure.bind_congr_right (he.mono (fun _ h => h.2)),C.rational.mean]

include C in
omit [IsProbabilityMeasure P] in
lemma CanonicalMass.deterministic_green_kernel (t : ℝ≥0) (E : Set Ω)
    (hE : MeasurableSet[(Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) t] E) :
    (P.restrict E).bind C.rational.terminal=(P.restrict E).bind (C.process t)+
      (P.restrict E).bind (halfPlaneGreenMeasure κ B γ G t) := by
  let ℱ := Filtration.natural B (fun s =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)
  have hs := isStoppingTime_const ℱ t
  have hEs : MeasurableSet[hs.measurableSpace] E := by
    change MeasurableSet[(isStoppingTime_const ℱ t).measurableSpace] E
    rw [IsStoppingTime.measurableSpace_const]
    exact hE
  have h := C.kernel (fun _ => (t:WithTop ℝ≥0)) hs E hEs
  change (P.restrict E).bind C.rational.terminal=(P.restrict E).bind (C.process t)+
    (P.restrict E).bind (halfPlaneGreenMeasure κ B γ G t) at h
  exact h

include C hB hc R he c hcp in
lemma CanonicalMass.scaledRawMass_cross_kernel
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0) (E : Set Ω)
    (hE : MeasurableSet[(Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) t] E) :
    (P.restrict E).bind (fun ω => dilationMass κ c hcp (C.rational.terminal ω))+
      (P.restrict E).bind (scaledRawMass R c B hc t)=
    (P.restrict E).bind (scaledRawTerminal R c B hc)+
      (P.restrict E).bind (fun ω => dilationMass κ c hcp (C.process t ω)) := by
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  have hCm := C.progressive.adapted.measurable (i:=t)
  have hGm := halfPlaneGreenMeasure_measurable hBm hc κ γ G F hw t
  have hdm : Measurable (dilationMass κ c hcp) := conformalMass_measurable _ _
  have hNm := (scaledRawMass_adapted R c hcp B hm hc).measurable (i:=t)
  have hd := congrArg (dilationMass κ c hcp) (C.deterministic_green_kernel t E hE)
  change dilationMass κ c hcp ((P.restrict E).bind C.rational.terminal)=
    conformalMass (halfPlaneDilation c hcp) _
      ((P.restrict E).bind (C.process t)+(P.restrict E).bind (halfPlaneGreenMeasure κ B γ G t)) at hd
  rw [conformalMass_add] at hd
  change dilationMass κ c hcp ((P.restrict E).bind C.rational.terminal)=
    dilationMass κ c hcp ((P.restrict E).bind (C.process t))+
      dilationMass κ c hcp ((P.restrict E).bind (halfPlaneGreenMeasure κ B γ G t)) at hd
  rw [← dilationMass_bind _ _ _ _ _ C.rational.terminal_measurable,
    ← dilationMass_bind _ _ _ _ _ hCm,← dilationMass_bind _ _ _ _ _ hGm] at hd
  have hr := C.raw_scaled_green_kernel hB hc F hw R he c hcp t E hE
  dsimp only at hr
  simp_rw [canonicalGreenMass_scaled κ B hc γ G F hw c hcp t] at hr
  change (P.restrict E).bind (scaledRawTerminal R c B hc)=
    (P.restrict E).bind (fun ω => scaledRawMass R c B hc t ω+
      dilationMass κ c hcp (halfPlaneGreenMeasure κ B γ G t ω)) at hr
  have hD : Measurable (fun ω => dilationMass κ c hcp (halfPlaneGreenMeasure κ B γ G t ω)) :=
    hdm.comp hGm
  rw [bind_kernel_add _ _ _ hNm hD] at hr
  rw [hd,hr]
  ac_rfl

end SLEExactGauge.Multipoint

end

end OAI
