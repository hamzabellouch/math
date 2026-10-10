import OAI.Probability.SLE.Mass.StrictPastMass

namespace OAI

/-! The finite first-success partition in the strict past-mass identity.
A later successful test outside the visited trace is detected by its first
successful predecessor, whose entire event is already in that earlier past. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
attribute [local instance] Classical.propDecidable

namespace SLEExactGauge.Multipoint

variable {Ω : Type*}

def firstPastSuccess (I : Finset ℝ≥0) (E : ℝ≥0 → Set Ω) (t : ℝ≥0) : Set Ω :=
  E t \ ⋃ s ∈ I.filter (fun s => s < t), E s

lemma mem_firstPastSuccess_iff (I : Finset ℝ≥0) (E : ℝ≥0 → Set Ω) (t : ℝ≥0) (ω : Ω) :
    ω∈firstPastSuccess I E t ↔ ω∈E t ∧ ∀ s∈I, s < t → ω∉E s := by
  simp [firstPastSuccess]

lemma exists_firstPastSuccess (I : Finset ℝ≥0) (E : ℝ≥0 → Set Ω) (ω : Ω)
    (h : ∃ t∈I, ω∈E t) :
    ∃ t∈I, ω∈firstPastSuccess I E t ∧ ∀ s∈I, ω∈E s → t ≤ s := by
  classical
  let J := I.filter (fun t => ω∈E t)
  have hJ : J.Nonempty := by
    obtain ⟨t,ht,hE⟩ := h
    exact ⟨t,Finset.mem_filter.mpr ⟨ht,hE⟩⟩
  let t := J.min' hJ
  have ht : t∈J := Finset.min'_mem J hJ
  refine ⟨t,(Finset.mem_filter.mp ht).1,?_,?_⟩
  · rw [mem_firstPastSuccess_iff]
    refine ⟨(Finset.mem_filter.mp ht).2,?_⟩
    intro s hs hst hEs
    exact (not_le_of_gt hst) (Finset.min'_le J s (Finset.mem_filter.mpr ⟨hs,hEs⟩))
  · intro s hs hEs
    exact Finset.min'_le J s (Finset.mem_filter.mpr ⟨hs,hEs⟩)

lemma firstPastSuccess_disjoint (I : Finset ℝ≥0) (E : ℝ≥0 → Set Ω)
    {s t : ℝ≥0} (hs : s∈I) (ht : t∈I) (hne : s≠t) :
    Disjoint (firstPastSuccess I E s) (firstPastSuccess I E t) := by
  rw [Set.disjoint_left]
  intro ω hωs hωt
  rw [mem_firstPastSuccess_iff] at hωs hωt
  rcases lt_or_gt_of_ne hne with hst | hts
  · exact hωt.2 s hs hst hωs.1
  · exact hωs.2 t ht hts hωt.1

lemma firstPastSuccess_measurable [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ) (I : Finset ℝ≥0) (E : ℝ≥0 → Set Ω)
    (hE : ∀ t∈I, MeasurableSet[ℱ t] (E t)) {t : ℝ≥0} (ht : t∈I) :
    MeasurableSet[ℱ t] (firstPastSuccess I E t) := by
  classical
  apply (hE t ht).diff
  apply Finset.measurableSet_biUnion
  intro s hs
  obtain ⟨hs,hst⟩ := Finset.mem_filter.mp hs
  exact (ℱ.mono hst.le) _ (hE s hs)

lemma firstPastSuccess_future_union {X : Type*}
    (I : Finset ℝ≥0) (E : ℝ≥0 → Set Ω) (A : ℝ≥0 → Set X) (hA : Monotone A) (ω : Ω) :
    (⋃ t∈I, if ω∈E t then (A t)ᶜ else ∅)=
      ⋃ t∈I, if ω∈firstPastSuccess I E t then (A t)ᶜ else ∅ := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨t,ht,hz⟩ := mem_iUnion₂.mp hz
    split_ifs at hz with hEt
    · obtain ⟨s,hs,hEs,hst⟩ := exists_firstPastSuccess I E ω ⟨t,ht,hEt⟩
      apply mem_iUnion₂.mpr
      refine ⟨s,hs,?_⟩
      rw [ite_eq_left hEs]
      exact fun hzs => hz (hA (hst t ht hEt) hzs)
    · exact False.elim (notMem_empty z hz)
  · intro hz
    obtain ⟨t,ht,hz⟩ := mem_iUnion₂.mp hz
    split_ifs at hz with hEt
    · apply mem_iUnion₂.mpr
      refine ⟨t,ht,?_⟩
      rw [ite_eq_left ((mem_firstPastSuccess_iff I E t ω).mp hEt).1]
      exact hz
    · exact False.elim (notMem_empty z hz)

lemma firstPastSuccess_unique (I : Finset ℝ≥0) (E : ℝ≥0 → Set Ω) (ω : Ω)
    {s t : ℝ≥0} (hs : s∈I) (ht : t∈I)
    (hωs : ω∈firstPastSuccess I E s) (hωt : ω∈firstPastSuccess I E t) : s=t := by
  by_contra hne
  exact Set.disjoint_left.mp (firstPastSuccess_disjoint I E hs ht hne) hωs hωt

lemma firstPastSuccess_future_mass {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (K : Set X) (I : Finset ℝ≥0) (E : ℝ≥0 → Set Ω)
    (A : ℝ≥0 → Set X) (hA : Monotone A) (ω : Ω) :
    μ (K ∩ ⋃ t∈I, if ω∈E t then (A t)ᶜ else ∅)=
      ∑ t∈I, if ω∈firstPastSuccess I E t then μ (K \ A t) else 0 := by
  classical
  rw [firstPastSuccess_future_union I E A hA ω]
  by_cases hex : ∃ t∈I, ω∈E t
  · obtain ⟨s,hs,hωs,_⟩ := exists_firstPastSuccess I E ω hex
    have he : (⋃ t∈I, if ω∈firstPastSuccess I E t then (A t)ᶜ else ∅)=(A s)ᶜ := by
      ext z
      constructor
      · intro hz
        obtain ⟨t,ht,hz⟩ := mem_iUnion₂.mp hz
        split_ifs at hz with hωt
        · have hts := firstPastSuccess_unique I E ω ht hs hωt hωs
          simpa only [hts] using hz
        · exact False.elim (notMem_empty z hz)
      · intro hz
        exact mem_iUnion₂.mpr ⟨s,hs,by simpa only [ite_eq_left hωs] using hz⟩
    rw [he]
    symm
    rw [Finset.sum_eq_single s]
    · simp only [ite_eq_left hωs,sdiff_eq_compl_inter,inter_comm]
    · intro t ht hts
      have hnot : ω∉firstPastSuccess I E t := fun h => hts (firstPastSuccess_unique I E ω ht hs h hωs)
      simp only [ite_eq_right hnot]
    · exact fun h => False.elim (h hs)
  · have hn (t) (ht : t∈I) : ω∉firstPastSuccess I E t :=
      fun h => hex ⟨t,ht,((mem_firstPastSuccess_iff I E t ω).mp h).1⟩
    have he : (⋃ t∈I, if ω∈firstPastSuccess I E t then (A t)ᶜ else ∅)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨t,ht,hz⟩ := mem_iUnion₂.mp hz
      simp only [ite_eq_right (hn t ht),notMem_empty] at hz
    rw [he,inter_empty,measure_empty]
    symm
    exact Finset.sum_eq_zero (fun t ht => by simp only [ite_eq_right (hn t ht)])

end SLEExactGauge.Multipoint

end

end OAI
