import OAI.Analysis.LipschitzHilbert.Trees.SourceBlockPathMass

namespace OAI

/-! Choose the actual continuing path child when it exists. In the terminal
block any existing child may be used as the graph exception, since the path
drop is one. A genuinely empty child family remains a separate case. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

theorem sourceBlock_exists_path_exception {ι X : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (weight : ι → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 < weight t x) (hK : 0 < K) (σ : Fin K) (j : ℕ)
    (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ j))
    (hne : (g.sourceBlockCells tops slope precision cutoff (ShiftedBlocks.endpoint σ j)
      (ShiftedBlocks.endpoint σ (j+1))
      (g.index (ShiftedBlocks.endpoint σ j) (slope top))).Nonempty) :
    ∃ i₀ : g.sourceBlockCells tops slope precision cutoff (ShiftedBlocks.endpoint σ j)
        (ShiftedBlocks.endpoint σ (j+1))
        (g.index (ShiftedBlocks.endpoint σ j) (slope top)),
      ∀ x : X,
      let n := g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ j)
        (g.index (ShiftedBlocks.endpoint σ j) (slope top)) x
      let c := fun i => g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ (j+1)) i x
      let u := pathDrop (g.shiftedPathMass tops slope precision cutoff weight σ top x) j
      1-c i₀.val/n ≤ u ∧ (∑ i : PhaseCombinatorics.RemainderIndex i₀, c i.val.val/n) ≤ u := by
  by_cases hnext : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ (j+1))
  · let i₀ : g.sourceBlockCells tops slope precision cutoff (ShiftedBlocks.endpoint σ j)
        (ShiftedBlocks.endpoint σ (j+1)) (g.index (ShiftedBlocks.endpoint σ j) (slope top)) :=
      ⟨g.index (ShiftedBlocks.endpoint σ (j+1)) (slope top),
        g.mem_sourceBlockCells_of_top tops slope precision cutoff _ _ _ hp
          ((ShiftedBlocks.endpoint_strictMono hK σ).monotone (Nat.le_succ j)) top htop rfl hnext⟩
    refine ⟨i₀,fun x => ?_⟩
    have h := g.sourceBlock_continuing_drop tops slope precision cutoff weight hp hw hK σ j
      top htop hnext x i₀ rfl
    exact ⟨h.1.le,h.2⟩
  · obtain ⟨i,hi⟩ := hne
    refine ⟨⟨i,hi⟩,fun x => ?_⟩
    exact g.sourceBlock_terminal_drop tops slope precision cutoff weight hp hw hK σ j
      top htop he hnext x ⟨i,hi⟩

end LipschitzHilbert.AngularGrid

end

end OAI
