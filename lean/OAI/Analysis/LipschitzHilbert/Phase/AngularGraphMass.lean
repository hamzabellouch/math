import OAI.Analysis.LipschitzHilbert.Phase.AngularBoundary
import OAI.Analysis.LipschitzHilbert.Geometry.LocalMinimaSelection

namespace OAI

/-! Actual boundary masses dominate the graph's closed-neighborhood mass. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.AngularGrid

theorem closed_neighborhood_mass_le_boundary {ι X : Type*}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ i ∈ tops, 0 ≤ precision i) (hw : ∀ i x, 0 ≤ weight i x)
    {base level : ℕ} (hle : base ≤ level) {gap : ℝ} (hgap : 0 ≤ gap)
    (cells : Finset ℤ) (representative : cells → ℝ) (parent : ℤ)
    (hcell : ∀ c, g.index (level + 1) (representative c) = c.val)
    (hancestor : ∀ c, g.index base (representative c) = parent)
    (i : cells) (x : X) :
    orderMass (fun c : cells => g.mass tops slope precision cutoff weight (level + 1) c.val x)
      (closedNeighborhood (fun c e : cells => g.neighbors (level + 1) gap c.val e.val) i) ≤
      g.boundaryMass tops slope precision cutoff weight base level gap (representative i) x := by
  classical
  let neighbors := closedNeighborhood
    (fun c e : cells => g.neighbors (level + 1) gap c.val e.val) i
  have hsub : ∀ c ∈ neighbors.image Subtype.val,
      g.cellTops tops slope precision cutoff (level + 1) c ⊆
        g.boundaryTops tops slope precision cutoff base level gap (representative i) := by
    intro c hc
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    have hnear : g.neighbors (level + 1) gap i.val j.val := by
      obtain hji | hij := (mem_closedNeighborhood _ _ _).mp hj
      · subst j
        unfold AngularGrid.neighbors
        simp only [sub_self, abs_zero]
        linarith [g.width_pos (level + 1)]
      · exact hij
    have h := g.neighbor_cell_subset_boundary tops slope precision cutoff hp hle
      gap (representative i) (representative j)
      ((hancestor j).trans (hancestor i).symm)
      (by simpa only [hcell] using hnear)
    simpa only [hcell] using h
  have h := g.sum_cell_mass_le_boundary tops slope precision cutoff weight hw
    base level gap (representative i) (neighbors.image Subtype.val) hsub x
  rw [Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)] at h
  exact h

end LipschitzHilbert.AngularGrid

end

end OAI
