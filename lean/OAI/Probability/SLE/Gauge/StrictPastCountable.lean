import OAI.Probability.SLE.Gauge.StrictPastExpectation

namespace OAI

/-! Countable exhaustion of the strict past-mass identity. -/

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

lemma finite_strict_past_mass_aemeasurable (I : Finset ℝ≥0) (E : ℝ≥0 → Set Ω)
    (hE : ∀ t∈I, MeasurableSet[(Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) t] (E t))
    (K : Set upperHalfPlane) (hK : IsCompact K) :
    AEMeasurable (fun ω => C.rational.terminal ω (K ∩ ⋃ t∈I,
      if ω∈E t then {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 t}ᶜ else ∅)) P := by
  let ℱ := Filtration.natural B (fun s =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)
  let f (t : ℝ≥0) := (firstPastSuccess I E t).indicator (fun ω => C.rational.terminal ω
    (K \ {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 t}))
  have hf (t) (ht : t∈I) : AEMeasurable (f t) P :=
    (C.strict_past_mass_aemeasurable hB hc h0 hκ hκ8 F hw t K hK).indicator
      ((ℱ.le t) _ (firstPastSuccess_measurable ℱ I E hE ht))
  have hm := I.aemeasurable_sum hf
  apply hm.congr
  filter_upwards [] with ω
  simp only [Finset.sum_apply]
  symm
  simpa only [f,Set.indicator,mem_ofPred_eq] using firstPastSuccess_future_mass
    (C.rational.terminal ω) K I E
    (fun t => {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 t})
    (fun s t hst z hz => by
      obtain ⟨r,hr,he⟩ := hz
      exact ⟨r,⟨hr.1,hr.2.trans hst⟩,he⟩) ω

lemma countable_strict_past_expectation (J : ℕ → Finset ℝ≥0) (hJ : Monotone J)
    (E : ℝ≥0 → Set Ω)
    (hE : ∀ t, MeasurableSet[(Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) t] (E t))
    (K : Set upperHalfPlane) (hK : IsCompact K) :
    (∫⁻ ω, C.rational.terminal ω (K ∩ ⋃ n, ⋃ t∈J n,
      if ω∈E t then {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 t}ᶜ else ∅) ∂P)=
      ⨆ n, ∑ t∈J n, ∫⁻ ω in firstPastSuccess (J n) E t,
        halfPlaneGreenMeasure κ B γ G t ω K ∂P := by
  let A (n : ℕ) (ω : Ω) := K ∩ ⋃ t∈J n,
    if ω∈E t then {z : upperHalfPlane | (z:ℂ)∈γ ω '' Icc 0 t}ᶜ else ∅
  have hAm (ω) : Monotone (fun n => A n ω) := by
    intro n m hnm z hz
    obtain ⟨hzK,hz⟩ := hz
    obtain ⟨t,ht,hzt⟩ := mem_iUnion₂.mp hz
    exact ⟨hzK,mem_iUnion₂.mpr ⟨t,hJ hnm ht,hzt⟩⟩
  have hfm (n) : AEMeasurable (fun ω => C.rational.terminal ω (A n ω)) P :=
    C.finite_strict_past_mass_aemeasurable hB hc h0 hκ hκ8 F hw (J n) E (fun t _ => hE t) K hK
  calc
    _ = ∫⁻ ω, ⨆ n, C.rational.terminal ω (A n ω) ∂P := by
      apply lintegral_congr
      intro ω
      rw [inter_iUnion]
      exact (hAm ω).measure_iUnion
    _ = ⨆ n, ∫⁻ ω, C.rational.terminal ω (A n ω) ∂P :=
      lintegral_iSup' hfm (Eventually.of_forall (fun ω n m hnm => measure_mono (hAm ω hnm)))
    _ = _ := iSup_congr (fun n => C.finite_strict_past_expectation hB hc h0 hκ hκ8 F hw
      (J n) E (fun t _ => hE t) K hK)

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
