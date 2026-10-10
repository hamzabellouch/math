import OAI.Analysis.LipschitzHilbert.Geometry.RectangleCoverSelection

namespace OAI

/-! A finite subfamily of a selection run has a last member. All the
other members were present in its actual previous set. -/
noncomputable section
open Set
namespace LipschitzHilbert.RectangleCoverRun
variable {ι : Type*} [DecidableEq ι]
variable {R : ι → Rectangle} {blocked : Finset ι → ι → Prop}
  {previous stock : Finset ι} {selected : List ι}

theorem last_selected_witness (h : RectangleCoverRun R blocked previous stock selected)
    (s : Finset ι) (hs : s.Nonempty) (hsub : s ⊆ selected.toFinset) :
    ∃ r ∈ s, ∃ p : Finset ι, previous ⊆ p ∧ s.erase r ⊆ p ∧ ¬blocked p r := by
  induction h generalizing s with
  | stop previous => simpa using hsub hs.choose_spec
  | step previous stock i tail hi hp ha htail ih =>
    have ht : s.erase i ⊆ tail.toFinset := by
      intro j hj
      have hj' := Finset.mem_erase.mp hj
      have hh := hsub hj'.2
      simp only [List.toFinset_cons,Finset.mem_insert] at hh
      exact hh.resolve_left hj'.1
    by_cases hn : (s.erase i).Nonempty
    · obtain ⟨r,hr,p,hp0,hsp,hb⟩ := ih (s.erase i) hn ht
      have hrs := (Finset.mem_erase.mp hr).2
      refine ⟨r,hrs,p,(Finset.subset_insert _ _).trans hp0,?_,hb⟩
      intro j hj
      by_cases hji : j = i
      · subst j
        exact hp0 (Finset.mem_insert_self _ _)
      · exact hsp (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1,
          Finset.mem_erase.mpr ⟨hji,(Finset.mem_erase.mp hj).2⟩⟩)
    · have he : s.erase i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      have his : i ∈ s := by
        obtain ⟨j,hj⟩ := hs
        by_contra hni
        have hji : j ≠ i := by intro h; subst j; exact hni hj
        have hh := Finset.mem_erase.mpr ⟨hji,hj⟩
        rw [he] at hh
        exact Finset.notMem_empty j hh
      exact ⟨i,his,previous,Subset.rfl,by simp [he],ha⟩

/-- Every strictly longer selected rectangle precedes the specified
member and belongs to the previous set at its selection. -/
theorem selected_previous_witness (h : RectangleCoverRun R blocked previous stock selected)
    (r : ι) (hr : r ∈ selected) :
    ∃ p : Finset ι, previous ⊆ p ∧
      (∀ j ∈ selected, (R r).long < (R j).long → j ∈ p) ∧ ¬blocked p r := by
  induction h with
  | stop => simp at hr
  | step previous stock i tail hi hp ha htail ih =>
    rcases List.mem_cons.mp hr with hri | hrt
    · subst r
      refine ⟨previous,Subset.rfl,?_,ha⟩
      intro j hj hlong
      rcases List.mem_cons.mp hj with rfl | hjt
      · exact (lt_irrefl _ hlong).elim
      · have hjs := rectangleRemaining_subset blocked previous stock i (htail.selected_subset j hjt)
        exact (not_lt_of_ge (hp j hjs).1 hlong).elim
    · obtain ⟨p,hprev,hpLong,hnot⟩ := ih hrt
      refine ⟨p,(Finset.subset_insert _ _).trans hprev,?_,hnot⟩
      intro j hj hjlong
      rcases List.mem_cons.mp hj with rfl | hjt
      · exact hprev (Finset.mem_insert_self _ _)
      · exact hpLong j hjt hjlong

end LipschitzHilbert.RectangleCoverRun

end

end OAI
