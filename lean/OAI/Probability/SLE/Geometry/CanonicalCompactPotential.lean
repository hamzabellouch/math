import OAI.Probability.SLE.Geometry.WeightedCompactKernel
import OAI.Probability.SLE.Mass.CanonicalMassFirstVisit
import OAI.Probability.SLE.Geometry.CanonicalGreenPast

namespace OAI

/-! The current Green potential of a compact weighted mass is the
conditional expectation of its remaining terminal mass. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint

local instance compactPotentialDriverMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance compactPotentialDriverBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

lemma compactWeightedMass_add
    (w : C(upperHalfPlane,ℝ≥0)) (K : Set upperHalfPlane) (hK : IsCompact K)
    (μ ν : Measure upperHalfPlane)
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] :
    compactWeightedMass w K (μ+ν)=compactWeightedMass w K μ+compactWeightedMass w K ν := by
  unfold compactWeightedMass
  rw [Measure.restrict_add]
  exact integral_add_measure (compact_weight_integrable w K hK μ)
    (compact_weight_integrable w K hK ν)

lemma halfPlaneGreenMeasure_measurable_past
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0) :
    Measurable[(Filtration.natural B (fun s => (hm s).stronglyMeasurable)) t]
      (halfPlaneGreenMeasure κ B γ G t) := by
  let ℱ := Filtration.natural B (fun s => (hm s).stronglyMeasurable)
  have hp : Measurable[ℱ t,driverPathFiltration t] (sourceDriverPath B hc) :=
    driverPath_measurable_past_of_adapted ℱ _
      (fun s => (Filtration.stronglyAdapted_natural (fun s => (hm s).stronglyMeasurable) s).measurable) t
  have h := (canonicalGreenMass_measurable_past κ t).comp hp
  convert h using 1
  funext ω
  exact (canonicalGreenMass_eq κ (sourceDriverPath B hc ω) (hw ω) t).symm

namespace CanonicalMass

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

lemma compact_potential_condExp
    (hc : ∀ ω, Continuous (fun t => B t ω)) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (w : C(upperHalfPlane,ℝ≥0)) (K : Set upperHalfPlane) (hK : IsCompact K)
    (t : ℝ≥0) :
    (fun ω => compactWeightedMass w K (halfPlaneGreenMeasure κ B γ G t ω)) =ᵐ[P]
      P[(fun ω => compactWeightedMass w K (C.rational.terminal ω)-
        compactWeightedMass w K (C.process t ω)) |
          (Filtration.natural B (fun r =>
            (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)) t] := by
  let ℱ := Filtration.natural B (fun r =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)
  let V := halfPlaneGreenMeasure κ B γ G t
  have hVp : Measurable[ℱ t] V := halfPlaneGreenMeasure_measurable_past
    (fun r => hBm.comp (measurable_const.prodMk measurable_id)) hc κ γ G F hw t
  have hVm : Measurable V := hVp.mono (ℱ.le t) le_rfl
  have hk (E : Set Ω) (hE : MeasurableSet[ℱ t] E) :
      (P.restrict E).bind C.rational.terminal =
        (P.restrict E).bind (C.process t)+(P.restrict E).bind V := by
    have hs := isStoppingTime_const ℱ t
    have hES : MeasurableSet[hs.measurableSpace] E := by
      rw [IsStoppingTime.measurableSpace_const]
      exact hE
    have h := C.kernel (fun _ => (t:WithTop ℝ≥0)) hs E hES
    change (P.restrict E).bind C.rational.terminal =
      (P.restrict E).bind (C.process t)+
        (P.restrict E).bind (halfPlaneStoppingGreenMeasure κ B γ G (fun _ => (t:ℝ≥0∞))) at h
    rwa [halfPlaneStoppingGreenMeasure_const] at h
  have hVbound (E : Set Ω) (hE : MeasurableSet[ℱ t] E) :
      (P.restrict E).bind V ≤ initialGreenMeasure κ := by
    apply le_trans _ (C.uniqueness_terminal_mean_le E)
    rw [hk E hE]
    exact Measure.le_add_left le_rfl
  have hVL := compactWeightedMass_kernel_integrable P κ V hVm
    (by simpa only [Measure.restrict_univ] using hVbound univ MeasurableSet.univ) w K hK
  have hNL := compactWeightedMass_kernel_integrable P κ (C.process t)
    C.progressive.adapted.measurable
    (by simpa only [Measure.restrict_univ] using C.uniqueness_process_mean_le t univ) w K hK
  have hTL := compactWeightedMass_kernel_integrable P κ C.rational.terminal
    C.rational.terminal_measurable (by rw [C.rational.mean]) w K hK
  apply ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le t) (hTL.1.sub hNL.1)
    (fun E _ _ => hVL.1.integrableOn) ?_
    (((compactWeightedMass_measurable w K hK.measurableSet).comp hVp).aestronglyMeasurable)
  intro E hE _
  have hVE := (compactWeightedMass_kernel_integrable (P.restrict E) κ V hVm (hVbound E hE) w K hK).2
  have hNE := (compactWeightedMass_kernel_integrable (P.restrict E) κ (C.process t)
    C.progressive.adapted.measurable (C.uniqueness_process_mean_le t E) w K hK).2
  have hTE := (compactWeightedMass_kernel_integrable (P.restrict E) κ C.rational.terminal
    C.rational.terminal_measurable (C.uniqueness_terminal_mean_le E) w K hK).2
  let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
  let : IsFiniteMeasureOnCompacts ((P.restrict E).bind (C.process t)) :=
    ⟨fun A hA => lt_of_le_of_lt (C.uniqueness_process_mean_le t E A) hA.measure_lt_top⟩
  let : IsFiniteMeasureOnCompacts ((P.restrict E).bind V) :=
    ⟨fun A hA => lt_of_le_of_lt (hVbound E hE A) hA.measure_lt_top⟩
  simp only [Pi.sub_apply]
  rw [integral_sub hTL.1.integrableOn hNL.1.integrableOn,hVE,hTE,hNE,hk E hE,
    compactWeightedMass_add w K hK]
  ring

end CanonicalMass
end SLEExactGauge.Multipoint

end

end OAI
