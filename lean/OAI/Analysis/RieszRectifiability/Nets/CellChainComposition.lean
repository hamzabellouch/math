import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.CellChainGeometry

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem SupportCellDescendant.eq_of_common_point_same_depth {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i j : SupportCellDescendant μ R hR k z) (hdepth : i.depth = j.depth)
    (x : Ambient d) (hi : x ∈ i.cell) (hj : x ∈ j.cell) : i = j := by
  rcases i with ⟨ti, xi, hxi, hai⟩
  rcases j with ⟨tj, xj, hxj, haj⟩
  change ti = tj at hdepth
  subst tj
  have heq : (⟨xi, hxi⟩ : (supportLatticeNets μ R hR (k + ti)).points) = ⟨xj, hxj⟩ := by
    by_contra hne
    exact Set.disjoint_left.mp (cleanSupportCell_disjoint μ R hR (k + ti) _ _ hne) hi hj
  have hx : xi = xj := congrArg Subtype.val heq
  subst xj
  rfl

theorem SupportCellDescendant.cell_nested_of_common_point {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i q : SupportCellDescendant μ R hR k z) (hq : q.depth ≤ i.depth)
    (x : Ambient d) (hi : x ∈ i.cell) (hqx : x ∈ q.cell) : i.cell ⊆ q.cell := by
  obtain ⟨j, hj, hsub, _⟩ := i.exists_ancestor_at_depth q.depth hq
  have heq := j.eq_of_common_point_same_depth q hj x (hsub hi) hqx
  simpa only [heq] using! hsub

theorem supportLatticeAncestor_eq_of_center_mem {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k t : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (w : (supportLatticeNets μ R hR (k + t)).points)
    (hw : (w : Ambient d) ∈ cleanSupportCell μ R hR k z) :
    supportLatticeAncestor μ R hR k t w = z := by
  have ht := cleanSupportCell_nested μ R hR k t w (center_mem_cleanSupportCell μ R hR (k + t) w)
  by_contra hne
  exact Set.disjoint_left.mp (cleanSupportCell_disjoint μ R hR k _ z hne) ht hw

def SupportCellDescendant.compose {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z)
    (j : SupportCellDescendant μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩) :
    SupportCellDescendant μ R hR k z where
  depth := i.depth + j.depth
  center := j.center
  mem_net := by rw [← Nat.add_assoc]; exact j.mem_net
  ancestor := by
    apply supportLatticeAncestor_eq_of_center_mem
    exact i.cell_subset_top (j.cell_subset_top j.center_mem_cell)

theorem SupportCellDescendant.compose_depth {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z)
    (j : SupportCellDescendant μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩) :
    (i.compose j).depth = i.depth + j.depth := rfl

theorem SupportCellDescendant.compose_cell {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z)
    (j : SupportCellDescendant μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩) :
    (i.compose j).cell = j.cell := by
  simp only [SupportCellDescendant.cell, SupportCellDescendant.compose,
    cleanSupportCell, supportLatticeCell, supportLatticeCenter, Nat.add_assoc]

theorem SupportCellDescendant.compose_radius {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i : SupportCellDescendant μ R hR k z)
    (j : SupportCellDescendant μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩) :
    (i.compose j).radius = j.radius := by
  simp only [SupportCellDescendant.radius, SupportCellDescendant.compose, Nat.add_assoc]

theorem SupportCellDescendant.exists_relative_descendant {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (i q : SupportCellDescendant μ R hR k z) (hi : i.depth ≤ q.depth)
    (hsub : q.cell ⊆ i.cell) :
    ∃ j : SupportCellDescendant μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩,
      j.depth = q.depth - i.depth ∧ j.center = q.center ∧ j.cell = q.cell ∧ j.radius = q.radius := by
  have hlevel : k + i.depth + (q.depth - i.depth) = k + q.depth := by omega
  let w : (supportLatticeNets μ R hR (k + i.depth + (q.depth - i.depth))).points :=
    ⟨q.center, by rw [hlevel]; exact q.mem_net⟩
  have hw : supportLatticeAncestor μ R hR (k + i.depth) (q.depth - i.depth) w =
      ⟨i.center, i.mem_net⟩ :=
    supportLatticeAncestor_eq_of_center_mem μ R hR (k + i.depth) (q.depth - i.depth)
      ⟨i.center, i.mem_net⟩ w (hsub q.center_mem_cell)
  let j : SupportCellDescendant μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩ :=
    { depth := q.depth - i.depth, center := q.center, mem_net := w.property, ancestor := hw }
  refine ⟨j, rfl, rfl, ?_, ?_⟩
  · simp only [SupportCellDescendant.cell, j, cleanSupportCell, supportLatticeCell,
      supportLatticeCenter, hlevel]
  · simp only [SupportCellDescendant.radius, j, hlevel]

end

end RieszRectifiability

end OAI
