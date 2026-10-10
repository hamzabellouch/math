import OAI.Probability.SLE.Geometry.RandomKernelSupport
import OAI.Probability.SLE.Mass.GreenMeasureSupport
import OAI.Probability.SLE.Geometry.CountableRemainderKernels

namespace OAI

/-! The positive remaining mass in the actual countable Radon construction
is carried by the surviving Loewner domain. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

lemma surviving_complement_past_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0) :
    @MeasurableSet (Ω × upperHalfPlane)
      ((Filtration.natural B (fun r => (hm r).stronglyMeasurable) t).prod inferInstance)
      {p | (p.2 : ℂ) ∉ survivingDomain (γ p.1) t} := by
  have hlive := (actual_spatial_past_kernels hm hBc κ γ G F hw t).2.2
  let : MeasurableSpace Ω := Filtration.natural B (fun r => (hm r).stronglyMeasurable) t
  let t0 : Iic t := ⟨t,by simp only [mem_Iic]; exact le_rfl⟩
  have hmap : Measurable (fun p : Ω × upperHalfPlane =>
      (t0,((p.2 : ℂ),p.1))) := by
    apply Measurable.prodMk
    · exact measurable_const
    · exact ((measurable_subtype_coe : Measurable (fun z : upperHalfPlane => (z : ℂ))).comp
        measurable_snd).prodMk measurable_fst
  exact (hlive.preimage hmap).compl

theorem ae_remainder_carried_by_surviving
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0) (η : Ω → Measure upperHalfPlane) (hη : Measurable η)
    (hηfin : ∀ ω, IsFiniteMeasureOnCompacts (η ω))
    (hevent : ∀ E : Set Ω,
      MeasurableSet[Filtration.natural B (fun r =>
        (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable) t] E →
      (P.restrict E).bind η = (P.restrict E).bind (halfPlaneGreenMeasure κ B γ G t)) :
    ∀ᵐ ω ∂P, η ω {z : upperHalfPlane | (z : ℂ) ∉ survivingDomain (γ ω) t} = 0 := by
  let D := localTestFamily upperHalfPlane
  let ℱ := Filtration.natural B (fun r =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)
  have hmean : P.bind η = P.bind (halfPlaneGreenMeasure κ B γ G t) := by
    simpa only [Measure.restrict_univ] using hevent univ MeasurableSet.univ
  let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
  refine ae_avoids_random_set_of_conditional_kernel (ℱ t) (ℱ.le t) P η
    (halfPlaneGreenMeasure κ B γ G t) hη
    (halfPlaneGreenMeasure_measurable hBm hBc κ γ G F hw t)
    D.compactSet (fun n => (D.isCompact n).measurableSet) ?_ ?_ ?_ ?_ hevent
    {p | (p.2 : ℂ) ∉ survivingDomain (γ p.1) t} ?_ ?_
  · intro z
    obtain ⟨n,hn⟩ := D.exhaustive {z} isCompact_singleton
    exact ⟨n,hn (mem_singleton z)⟩
  · intro n ω
    let := hηfin ω
    exact (D.isCompact n).measure_lt_top
  · intro n
    exact ae_halfPlaneGreenMeasure_compact_finite hB hBm hBc hB0 hκ hκ8 γ G F hw t
      _ (D.isCompact n)
  · intro n
    rw [hmean]
    have hb := halfPlaneGreenMeasure_mean_le hB hBm hBc hB0 hκ hκ8 γ G F hw t univ
      (D.compactSet n)
    rw [Measure.restrict_univ] at hb
    exact lt_of_le_of_lt hb (D.isCompact n).measure_lt_top
  · exact surviving_complement_past_measurable
      (fun r => hBm.comp (measurable_const.prodMk measurable_id)) hBc κ γ G F hw t
  · intro ω
    exact halfPlaneGreenMeasure_off_surviving ω (hw ω) t

end SLEExactGauge.Multipoint

end

end OAI
