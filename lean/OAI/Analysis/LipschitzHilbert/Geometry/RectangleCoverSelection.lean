import OAI.Analysis.LipschitzHilbert.Geometry.RectangleDilation

namespace OAI

/-! Finite selection with the exact length/eccentricity priority in the
Lacey--Li covering algorithm. The removal predicate will be instantiated
by containment in the auxiliary maximal-function level set. -/
noncomputable section
open MeasureTheory Set
namespace LipschitzHilbert
variable {ι : Type*}

def rectanglePriority (R : ι → Rectangle) (i j : ι) : Prop :=
  (R j).long≤(R i).long ∧
    ((R j).long=(R i).long → (R i).short/(R i).long≤(R j).short/(R j).long)

theorem rectangle_priority_exists (R : ι → Rectangle) (s : Finset ι) (hs : s.Nonempty) :
    ∃ i∈s, ∀ j∈s, rectanglePriority R i j := by
  classical
  obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image s (fun i => (R i).long) hs
  let t := s.filter (fun j => (R j).long=(R i).long)
  have ht : t.Nonempty := ⟨i,by simp [t,hi]⟩
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image t (fun j => (R j).short/(R j).long) ht
  have hjs := (Finset.mem_filter.mp hj).1
  have hji := (Finset.mem_filter.mp hj).2
  refine ⟨j,hjs,?_⟩
  intro k hk
  constructor
  · rw [hji]
    exact hmax k hk
  · intro hkj
    exact hmin k (by simp [t,hk,hkj,hji])

def rectangleRemaining [DecidableEq ι] (blocked : Finset ι → ι → Prop)
    (previous stock : Finset ι) (i : ι) : Finset ι := by
  classical
  exact stock.filter (fun j => j≠i ∧ ¬blocked (insert i previous) j)

theorem mem_rectangleRemaining [DecidableEq ι] (blocked : Finset ι → ι → Prop)
    (previous stock : Finset ι) (i j : ι) :
    j∈rectangleRemaining blocked previous stock i ↔ j∈stock ∧ j≠i ∧ ¬blocked (insert i previous) j := by
  classical
  simp only [rectangleRemaining,Finset.mem_filter]

theorem rectangleRemaining_subset [DecidableEq ι] (blocked : Finset ι → ι → Prop)
    (previous stock : Finset ι) (i : ι) : rectangleRemaining blocked previous stock i⊆stock := by
  classical
  exact Finset.filter_subset _ _

theorem rectangleRemaining_card_lt [DecidableEq ι] (blocked : Finset ι → ι → Prop)
    (previous stock : Finset ι) (i : ι) (hi : i∈stock) :
    (rectangleRemaining blocked previous stock i).card<stock.card := by
  classical
  apply Finset.card_lt_card
  apply (ssubset_iff_subset_ne).2
  refine ⟨rectangleRemaining_subset blocked previous stock i,?_⟩
  intro he
  have hm : i∈rectangleRemaining blocked previous stock i := he.symm ▸ hi
  exact (mem_rectangleRemaining blocked previous stock i i).mp hm |>.2.1 rfl

inductive RectangleCoverRun [DecidableEq ι] (R : ι → Rectangle) (blocked : Finset ι → ι → Prop) :
    Finset ι → Finset ι → List ι → Prop
  | stop (previous : Finset ι) : RectangleCoverRun R blocked previous ∅ []
  | step (previous stock : Finset ι) (i : ι) (tail : List ι)
      (hi : i∈stock) (hpriority : ∀ j∈stock, rectanglePriority R i j)
      (hallowed : ¬blocked previous i)
      (htail : RectangleCoverRun R blocked (insert i previous)
        (rectangleRemaining blocked previous stock i) tail) :
      RectangleCoverRun R blocked previous stock (i::tail)

theorem rectangle_cover_run_exists [DecidableEq ι] (R : ι → Rectangle)
    (blocked : Finset ι → ι → Prop) (stock previous : Finset ι)
    (hallowed : ∀ i∈stock, ¬blocked previous i) :
    ∃ selected, RectangleCoverRun R blocked previous stock selected := by
  classical
  induction stock using Finset.strongInduction generalizing previous with
  | H stock ih =>
    by_cases hs : stock=∅
    · subst stock
      exact ⟨[],RectangleCoverRun.stop previous⟩
    · obtain ⟨i,hi,hp⟩ := rectangle_priority_exists R stock (Finset.nonempty_iff_ne_empty.mpr hs)
      have hsub : rectangleRemaining blocked previous stock i⊂stock := by
        apply (ssubset_iff_subset_ne).2
        refine ⟨rectangleRemaining_subset blocked previous stock i,?_⟩
        intro he
        have hm : i∈rectangleRemaining blocked previous stock i := he.symm ▸ hi
        exact (mem_rectangleRemaining blocked previous stock i i).mp hm |>.2.1 rfl
      obtain ⟨tail,htail⟩ := ih _ hsub (insert i previous) (fun j hj =>
        ((mem_rectangleRemaining blocked previous stock i j).mp hj).2.2)
      exact ⟨i::tail,RectangleCoverRun.step previous stock i tail hi hp (hallowed i hi) htail⟩

namespace RectangleCoverRun
variable [DecidableEq ι] {R : ι → Rectangle} {blocked : Finset ι → ι → Prop}
  {previous stock : Finset ι} {selected : List ι}

theorem selected_subset (h : RectangleCoverRun R blocked previous stock selected) :
    ∀ i∈selected, i∈stock := by
  induction h with
  | stop => simp
  | step previous stock i tail hi _ _ htail ih =>
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hi
    · exact rectangleRemaining_subset blocked previous stock i (ih j hj)

theorem selected_nodup (h : RectangleCoverRun R blocked previous stock selected) : selected.Nodup := by
  induction h with
  | stop => simp
  | step previous stock i tail _ _ _ htail ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_,ih⟩
    intro hi
    have hm := htail.selected_subset i hi
    exact (mem_rectangleRemaining blocked previous stock i i).mp hm |>.2.1 rfl

theorem selected_priority (h : RectangleCoverRun R blocked previous stock selected) :
    selected.Pairwise (rectanglePriority R) := by
  induction h with
  | stop => exact List.Pairwise.nil
  | step previous stock i tail _ hp _ htail ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih⟩
    intro j hj
    exact hp j (rectangleRemaining_subset blocked previous stock i (htail.selected_subset j hj))


theorem rejected_blocked (h : RectangleCoverRun R blocked previous stock selected)
    (hmono : ∀ s t : Finset ι, s⊆t → ∀ i, blocked s i → blocked t i) :
    ∀ i∈stock, i∉selected → blocked (previous ∪ selected.toFinset) i := by
  classical
  induction h with
  | stop => simp
  | step previous stock r tail hr hp ha htail ih =>
    intro i hi hnot
    have hir : i≠r := by
      intro heq
      subst i
      exact hnot (List.mem_cons_self)
    have hint : i∉tail := fun hit => hnot (List.mem_cons_of_mem r hit)
    by_cases hn : i∈rectangleRemaining blocked previous stock r
    · have hh := ih i hn hint
      have heq : insert r previous ∪ tail.toFinset=previous ∪ (r::tail).toFinset := by
        ext j
        simp
      simpa only [heq] using hh
    · have hb : blocked (insert r previous) i := by
        by_contra hb
        exact hn ((mem_rectangleRemaining blocked previous stock r i).mpr ⟨hi,hir,hb⟩)
      apply hmono (insert r previous) (previous ∪ (r::tail).toFinset) _ i hb
      intro j hj
      simp only [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · simp
      · exact Finset.mem_union_left _ hj

end RectangleCoverRun
end LipschitzHilbert

end

end OAI
