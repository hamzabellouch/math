import OAI.Analysis.KadisonKastler.CountableUnitaryL2

namespace OAI

/-! Unitary multiplication preserves the specified coordinate sigma algebra. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X G K : Type*} [mX : MeasurableSpace X] {μ : Measure X}
  [MeasurableSpace G] [Countable G] [MeasurableSingletonClass G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace K]

theorem countableUnitaryAction_aestronglyMeasurable_sigma
    {m : MeasurableSpace X} (U : G → unitary (K →L[ℂ] K)) {c : X → G}
    (hc : Measurable[m] c) {f : X → K} (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (fun x => (U (c x) : K →L[ℂ] K) (f x)) μ := by
  borelize K
  have hm : Measurable (fun p : G × K => (U p.1 : K →L[ℂ] K) p.2) :=
    measurable_from_prod_countable_right (fun g => (U g : K →L[ℂ] K).continuous.measurable)
  refine ⟨fun x => (U (c x) : K →L[ℂ] K) (hf.mk f x), ?_, ?_⟩
  · exact (hm.comp (hc.prodMk hf.stronglyMeasurable_mk.measurable)).stronglyMeasurable
  · exact hf.ae_eq_mk.mono (fun x hx => congrArg (U (c x) : K →L[ℂ] K) hx)

theorem countableUnitaryL2_sigma {m : MeasurableSpace X}
    (U : G → unitary (K →L[ℂ] K)) {c : X → G} (hc : @Measurable X G mX _ c)
    (hcm : Measurable[m] c) (f : Lp K 2 μ) (hf : AEStronglyMeasurable[m] f μ) :
    AEStronglyMeasurable[m] (countableUnitaryL2 (mX := mX) (μ := μ) U hc f) μ := by
  let : MeasurableSpace X := mX
  exact (countableUnitaryAction_aestronglyMeasurable_sigma U hcm hf).congr
    (countableUnitaryL2_ae (mX := mX) (μ := μ) U hc f).symm

end

end KadisonKastler

end OAI
