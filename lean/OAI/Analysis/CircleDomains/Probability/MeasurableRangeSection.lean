import OAI.Analysis.CircleDomains.Selection.BaireRangeSection

namespace OAI

/-! A measurable map from a standard Borel space admits a section on its
image measurable for any fixed completed finite Borel measure. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

theorem exists_nullMeasurable_rangeSection
    {A Y : Type*} [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (K : A → Y) (hK : Measurable K) (μ : Measure Y) [IsFiniteMeasure μ] :
    ∃ s : Y → A, NullMeasurable s μ ∧ ∀ y ∈ range K, K (s y) = y := by
  let := upgradeStandardBorel A
  let graphMap : A → A × Y := fun a => (a, K a)
  have hg : AnalyticSet (range graphMap) := by
    simpa only [image_univ, graphMap, id_eq] using
      (MeasurableSet.univ.analyticSet_image (measurable_id.prodMk hK))
  rw [AnalyticSet] at hg
  obtain ⟨q, hq, hqr⟩ := hg.resolve_left (range_nonempty graphMap).ne_empty
  obtain ⟨b, hb, hbs⟩ := exists_nullMeasurable_baire_rangeSection μ
    (fun z => (q z).2) hq.snd
  refine ⟨fun y => (q (b y)).1, hq.fst.measurable.comp_nullMeasurable hb, ?_⟩
  intro y hy
  have hyr : y ∈ range (fun z => (q z).2) := by
    obtain ⟨a, rfl⟩ := hy
    have ha : graphMap a ∈ range q := hqr ▸ mem_range_self a
    obtain ⟨z, hz⟩ := ha
    exact ⟨z, congrArg Prod.snd hz⟩
  have hmem : q (b y) ∈ range graphMap := hqr.symm ▸ mem_range_self (b y)
  obtain ⟨a, ha⟩ := hmem
  have hfirst := congrArg Prod.fst ha
  have hsecond := congrArg Prod.snd ha
  change a = (q (b y)).1 at hfirst
  change K a = (q (b y)).2 at hsecond
  change K (q (b y)).1 = y
  rw [← hfirst, hsecond, hbs y hyr]

end CircleDomainRigidity

end

end OAI
