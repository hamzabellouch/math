import OAI.Analysis.LipschitzHilbert.Geometry.ProjectedPopularityPacking
import OAI.Analysis.LipschitzHilbert.Geometry.RectangleCoverSelection

namespace OAI

/-! The finite maximal-length grouping of overlapping projected
popularity sets used in the far-angle estimate. -/
noncomputable section
open Set
namespace LipschitzHilbert
variable {ι : Type*} [DecidableEq ι]

def projectionBlocked (P : ι → Set ℝ) (s : Finset ι) (j : ι) : Prop :=
  ∃ i ∈ s, (P i ∩ P j).Nonempty

omit [DecidableEq ι] in
theorem projectionBlocked_mono (P : ι → Set ℝ) {s t : Finset ι} (hst : s ⊆ t)
    (j : ι) (h : projectionBlocked P s j) : projectionBlocked P t j := by
  obtain ⟨i,hi,hij⟩ := h
  exact ⟨i,hst hi,hij⟩

theorem projection_group_run_exists (R : ι → Rectangle) (P : ι → Set ℝ) (s : Finset ι) :
    ∃ centers, RectangleCoverRun R (projectionBlocked P) ∅ s centers := by
  apply rectangle_cover_run_exists
  intro i _
  simp [projectionBlocked]

namespace RectangleCoverRun
variable {R : ι → Rectangle} {P : ι → Set ℝ} {previous stock : Finset ι} {centers : List ι}

theorem selected_unblocked_before (h : RectangleCoverRun R (projectionBlocked P) previous stock centers) :
    ∀ j ∈ centers, ¬projectionBlocked P previous j := by
  induction h with
  | stop => simp
  | step previous stock i tail hi hp ha htail ih =>
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact ha
    · intro hb
      exact ih j hj (projectionBlocked_mono P (Finset.subset_insert _ _) j hb)

theorem projected_centers_disjoint (h : RectangleCoverRun R (projectionBlocked P) previous stock centers) :
    centers.Pairwise (fun i j => Disjoint (P i) (P j)) := by
  induction h with
  | stop => exact List.Pairwise.nil
  | step previous stock i tail hi hp ha htail ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih⟩
    intro j hj
    apply Set.disjoint_iff_inter_eq_empty.mpr
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hn
    exact htail.selected_unblocked_before j hj ⟨i,Finset.mem_insert_self _ _,hn⟩

theorem projected_center_cover (h : RectangleCoverRun R (projectionBlocked P) previous stock centers)
    (hallowed : ∀ j ∈ stock, ¬projectionBlocked P previous j)
    (hnonempty : ∀ j ∈ stock, (P j).Nonempty) :
    ∀ j ∈ stock, ∃ i ∈ centers, (R j).long ≤ (R i).long ∧ (P i ∩ P j).Nonempty := by
  classical
  induction h with
  | stop => simp
  | step previous stock i tail hi hp ha htail ih =>
    intro j hj
    by_cases hji : j = i
    · subst j
      exact ⟨i,List.mem_cons_self,(hp i hi).1,by simpa only [inter_self] using hnonempty i hi⟩
    by_cases hjr : j ∈ rectangleRemaining (projectionBlocked P) previous stock i
    · obtain ⟨k,hkt,hlen,hint⟩ := ih
        (fun k hk => ((mem_rectangleRemaining (projectionBlocked P) previous stock i k).mp hk).2.2)
        (fun k hk => hnonempty k (rectangleRemaining_subset _ _ _ _ hk)) j hjr
      exact ⟨k,List.mem_cons_of_mem i hkt,hlen,hint⟩
    · have hb : projectionBlocked P (insert i previous) j := by
        by_contra hn
        exact hjr ((mem_rectangleRemaining (projectionBlocked P) previous stock i j).mpr ⟨hj,hji,hn⟩)
      obtain ⟨k,hk,hint⟩ := hb
      rcases Finset.mem_insert.mp hk with hki | hk
      · subst k
        exact ⟨i,List.mem_cons_self,(hp j hj).1,hint⟩
      · exact (hallowed j hj ⟨k,hk,hint⟩).elim

end RectangleCoverRun
end LipschitzHilbert

end

end OAI
