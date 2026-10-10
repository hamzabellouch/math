import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.RestartCoverageInduction
import OAI.Analysis.RieszRectifiability.Restart.ActiveCellChildImageMass
import OAI.Analysis.RieszRectifiability.Foundations.ImmediateChildPartition

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

variable {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
  {k : ℕ} {z : (supportLatticeNets μ R hR k).points}

def relativeRestartGood (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) :
    SupportCellDescendant μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩ → Prop :=
  fun i => ¬ Bad (q.compose i)

def relativeSelectedRestartStops (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d)) :
    Set (SupportCellDescendant μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩) :=
  {i | i ∈ cellRegionStops μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩
      (relativeRestartGood Bad q) ∧
    (i.depth = 0 ∨ ¬ Disjoint (closedBall i.center (i.radius / 32)) E)}

def selectedRestartParent (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d)) : Set (Ambient d) :=
  cellRegionLimit μ R hR (k + q.depth) ⟨q.center, q.mem_net⟩ (relativeRestartGood Bad q) ∩ E

def selectedRestartRemainder (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d)) : Set (Ambient d) :=
  q.cell \ (selectedRestartParent Bad q E ∪
    ⋃ i : relativeSelectedRestartStops Bad q E, i.val.cell)

def selectedRestartNext (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d)) :
    Set {w : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad w} :=
  {w | ∃ i : relativeSelectedRestartStops Bad q E,
    ∃ j : supportImmediateChildren μ R hR (k + q.depth + i.val.depth)
      ⟨i.val.center, i.val.mem_net⟩, w.val = q.compose (i.val.compose j.val)}

theorem selected_restart_child_is_restart
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d))
    (i : relativeSelectedRestartStops Bad q E)
    (j : supportImmediateChildren μ R hR (k + q.depth + i.val.depth)
      ⟨i.val.center, i.val.mem_net⟩) : cellRestartsAfter Bad (q.compose (i.val.compose j.val)) := by
  have hbad : Bad (q.compose i.val) := not_not.mp i.property.1.1
  have hj := (mem_supportImmediateChildren μ R hR _ _ j.val).mp j.property
  refine Or.inr ⟨q.compose i.val, hbad, ?_, ?_⟩
  · simp only [SupportCellDescendant.compose_depth, hj, Nat.add_assoc]
  · rw [SupportCellDescendant.compose_cell, SupportCellDescendant.compose_cell,
      SupportCellDescendant.compose_cell]
    exact j.val.cell_subset_top

theorem selected_restart_next_consumes_bad_cell
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d))
    (w : {w : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad w})
    (hw : w ∈ selectedRestartNext Bad q E) :
    ∃ i : SupportCellDescendant μ R hR k z,
      q.depth ≤ i.depth ∧ i.cell ⊆ q.cell ∧ Bad i ∧
        i.depth < w.val.depth ∧ w.val.cell ⊆ i.cell := by
  obtain ⟨i, j, hw⟩ := hw
  have hbad : Bad (q.compose i.val) := not_not.mp i.property.1.1
  have hj := (mem_supportImmediateChildren μ R hR _ _ j.val).mp j.property
  refine ⟨q.compose i.val, ?_, ?_, hbad, ?_, ?_⟩
  · rw [SupportCellDescendant.compose_depth]
    omega
  · rw [SupportCellDescendant.compose_cell]
    exact i.val.cell_subset_top
  · rw [hw, SupportCellDescendant.compose_depth, SupportCellDescendant.compose_depth,
      SupportCellDescendant.compose_depth, hj]
    omega
  · rw [hw, SupportCellDescendant.compose_cell, SupportCellDescendant.compose_cell,
      SupportCellDescendant.compose_cell]
    exact j.val.cell_subset_top

theorem selected_restart_partition
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (E : Set (Ambient d)) :
    q.cell \ selectedRestartRemainder Bad q E ⊆ selectedRestartParent Bad q E ∪
      ⋃ w : selectedRestartNext Bad q E, w.val.val.cell := by
  classical
  intro x hx
  have hret : x ∈ selectedRestartParent Bad q E ∪
      ⋃ i : relativeSelectedRestartStops Bad q E, i.val.cell := by
    by_contra hn
    exact hx.2 ⟨hx.1, hn⟩
  rcases hret with hp | hi
  · exact Or.inl hp
  · obtain ⟨i, hxi⟩ := mem_iUnion.mp hi
    have hxj : x ∈ ⋃ j : supportImmediateChildren μ R hR
        (k + q.depth + i.val.depth) ⟨i.val.center, i.val.mem_net⟩, j.val.cell :=
      cleanSupportCell_eq_immediate_children μ R hR _ _ ▸ hxi
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxj
    let w : {w : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad w} :=
      ⟨q.compose (i.val.compose j.val), selected_restart_child_is_restart Bad q E i j⟩
    have hw : w ∈ selectedRestartNext Bad q E := ⟨i, j, rfl⟩
    refine Or.inr (mem_iUnion.mpr ⟨⟨w, hw⟩, ?_⟩)
    change x ∈ (q.compose (i.val.compose j.val)).cell
    simpa only [SupportCellDescendant.compose_cell] using! hxj

end

end RieszRectifiability

end OAI
