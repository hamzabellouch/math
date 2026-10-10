import OAI.Probability.SLE.LoewnerCharts

namespace OAI

/-! One-sided time derivatives glue at a slit concatenation time. -/
noncomputable section
open Set Filter
open scoped Topology

namespace SLEExactGauge

lemma hasDerivWithinAt_time_splice
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : ℝ → E) (T t : ℝ) (d : E)
    (he : f T=g T)
    (hf : t ≤ T → HasDerivWithinAt f d (Ici 0) t)
    (hg : T ≤ t → HasDerivWithinAt g d (Ici T) t) :
    HasDerivWithinAt (fun s => if s ≤ T then f s else g s) d (Ici 0) t := by
  rcases lt_trichotomy t T with hlt | heq | hgt
  · apply (hf hlt.le).congr_of_eventuallyEq
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hlt)] with s hs
      exact ite_eq_left hs.le
    · exact ite_eq_left hlt.le
  · subst t
    have hl := (hf le_rfl).mono (show Ici 0 ∩ Iic T ⊆ Ici 0 from inter_subset_left)
    have hr := (hg le_rfl).mono (show Ici 0 ∩ Ici T ⊆ Ici T from inter_subset_right)
    have hl' : HasDerivWithinAt (fun s => if s ≤ T then f s else g s) d
        (Ici 0 ∩ Iic T) T := hl.congr (fun s hs => ite_eq_left hs.2) (ite_eq_left le_rfl)
    have hr' : HasDerivWithinAt (fun s => if s ≤ T then f s else g s) d
        (Ici 0 ∩ Ici T) T := by
      apply hr.congr
      · intro s hs
        by_cases h : s ≤ T
        · have hsT : s=T := le_antisymm h hs.2
          simpa only [hsT,ite_eq_left le_rfl] using he
        · exact ite_eq_right h
      · simpa only [ite_eq_left le_rfl] using he
    have hu : (Ici 0 ∩ Iic T) ∪ (Ici 0 ∩ Ici T)=Ici 0 := by
      ext s
      simp only [mem_union,mem_inter_iff,mem_Ici,mem_Iic]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro h
        exact (le_total s T).elim (fun hs => Or.inl ⟨h,hs⟩) (fun hs => Or.inr ⟨h,hs⟩)
    simpa only [hu] using hl'.union hr'
  · apply ((hg hgt.le).mono_of_mem_nhdsWithin ?_).congr_of_eventuallyEq
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (lt_mem_nhds hgt)] with s hs
      exact ite_eq_right (not_le.mpr hs)
    · exact ite_eq_right (not_le.mpr hgt)
    · exact mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds hgt)

end SLEExactGauge

end

end OAI
