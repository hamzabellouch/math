import OAI.Probability.SLE.Geometry.FirstSuccessfulPast

namespace OAI

/-! First-success partition for finite tests strictly before an extended time. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
attribute [local instance] Classical.propDecidable

namespace SLEExactGauge.Multipoint

variable {Ω : Type*}

def finiteStrictPastEvent (I : Finset ℝ≥0) (E : ℝ≥0 → Set Ω)
    (T : Ω → ℝ≥0∞) : Set Ω :=
  ⋃ t∈I, E t ∩ {ω | (t : ℝ≥0∞) < T ω}

lemma finiteStrictPastEvent_first (I : Finset ℝ≥0) (E : ℝ≥0 → Set Ω)
    (T : Ω → ℝ≥0∞) :
    finiteStrictPastEvent I E T =
      ⋃ t∈I, firstPastSuccess I E t ∩ {ω | (t : ℝ≥0∞) < T ω} := by
  ext ω
  constructor
  · intro h
    obtain ⟨t,ht,hEt,hT⟩ := mem_iUnion₂.mp h
    obtain ⟨s,hs,hEs,hst⟩ := exists_firstPastSuccess I E ω ⟨t,ht,hEt⟩
    exact mem_iUnion₂.mpr ⟨s,hs,hEs,(ENNReal.coe_le_coe.mpr (hst t ht hEt)).trans_lt hT⟩
  · intro h
    obtain ⟨t,ht,hEt,hT⟩ := mem_iUnion₂.mp h
    exact mem_iUnion₂.mpr ⟨t,ht,((mem_firstPastSuccess_iff I E t ω).mp hEt).1,hT⟩

lemma finiteStrictPastEvent_mono (I : Finset ℝ≥0) (E : ℝ≥0 → Set Ω)
    {S T : Ω → ℝ≥0∞} (h : S ≤ T) :
    finiteStrictPastEvent I E S ⊆ finiteStrictPastEvent I E T := by
  intro ω hω
  obtain ⟨t,ht,hEt,hT⟩ := mem_iUnion₂.mp hω
  exact mem_iUnion₂.mpr ⟨t,ht,hEt,hT.trans_le (h ω)⟩

lemma finiteStrictPastEvent_measurable [MeasurableSpace Ω]
    (I : Finset ℝ≥0) (E : ℝ≥0 → Set Ω) (hE : ∀ t∈I, MeasurableSet (E t))
    (T : Ω → ℝ≥0∞) (hT : Measurable T) : MeasurableSet (finiteStrictPastEvent I E T) :=
  Finset.measurableSet_biUnion I (fun t ht => (hE t ht).inter
    (measurableSet_lt measurable_const hT))

lemma finiteStrictPastEvent_measure [mΩ : MeasurableSpace Ω]
    (Q : Measure Ω) (ℱ : Filtration ℝ≥0 mΩ) (I : Finset ℝ≥0) (E : ℝ≥0 → Set Ω)
    (hE : ∀ t∈I, MeasurableSet[ℱ t] (E t))
    (T : Ω → ℝ≥0∞) (hT : Measurable T) :
    Q (finiteStrictPastEvent I E T) =
      ∑ t∈I, Q (firstPastSuccess I E t ∩ {ω | (t : ℝ≥0∞) < T ω}) := by
  rw [finiteStrictPastEvent_first]
  apply measure_biUnion_finset
  · intro s hs t ht hne
    exact (firstPastSuccess_disjoint I E hs ht hne).mono inter_subset_left inter_subset_left
  · intro t ht
    exact ((ℱ.le t) _ (firstPastSuccess_measurable ℱ I E hE ht)).inter
      (measurableSet_lt measurable_const hT)

end SLEExactGauge.Multipoint

end

end OAI
