import OAI.Analysis.LipschitzHilbert.Trees.SourceShiftedDrop
import OAI.Analysis.LipschitzHilbert.Trees.SourceCellMarking
import OAI.Analysis.LipschitzHilbert.Trees.SourceSnapshotWindow

namespace OAI

/-! Absolute path drops are sums over the actual lost tops. This gives
the cellwise relative motion needed by the source's infimum/supremum
marking rule, including a terminal block with no continuing path child. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

def shiftedPathLossTops {ι : Type*} {K : ℕ} (g : AngularGrid)
    (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (σ : Fin K) (top : ι) (j : ℕ) : Finset ι :=
  let parent := g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint σ j)
    (g.index (ShiftedBlocks.endpoint σ j) (slope top))
  if g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ (j+1)) then
    parent \ g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint σ (j+1))
      (g.index (ShiftedBlocks.endpoint σ (j+1)) (slope top))
  else parent

theorem shiftedPathLossTops_subset {ι : Type*} {K : ℕ} (g : AngularGrid)
    (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ)
    (σ : Fin K) (top : ι) (j : ℕ) :
    g.shiftedPathLossTops tops slope precision cutoff σ top j ⊆
      g.cellTops tops slope precision cutoff (ShiftedBlocks.endpoint σ j)
        (g.index (ShiftedBlocks.endpoint σ j) (slope top)) := by
  unfold shiftedPathLossTops
  split_ifs
  · exact Finset.sdiff_subset
  · exact Finset.Subset.refl _

theorem shiftedPathMass_difference {ι X : Type*} {K : ℕ} (g : AngularGrid)
    (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hK : 0 < K) (σ : Fin K)
    (top : ι) (j : ℕ)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ j)) (x : X) :
    g.shiftedPathMass tops slope precision cutoff weight σ top x j-
        g.shiftedPathMass tops slope precision cutoff weight σ top x (j+1) =
      ∑ t ∈ g.shiftedPathLossTops tops slope precision cutoff σ top j, weight t x := by
  rw [shiftedPathMass,ite_eq_left he]
  unfold shiftedPathLossTops
  split_ifs with hn
  · rw [shiftedPathMass,ite_eq_left hn]
    exact sub_eq_iff_eq_add.mpr (Finset.sum_sdiff (f := fun t => weight t x)
      (g.cellTops_subset_ancestor tops slope precision cutoff hp
        ((ShiftedBlocks.endpoint_strictMono hK σ).monotone (Nat.le_succ j)) (slope top))).symm
  · rw [shiftedPathMass,ite_eq_right hn,sub_zero]
    rfl

/-- Parent mass and absolute loss have the same relative motion bound:
each is a positive sum over a subset of the parent tops. -/
theorem source_shifted_absolute_motion {ι : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B Kw D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hKw : 0 < Kw) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (hK : 0 < K) (σ : Fin K) (j : ℕ) (top : ι)
    (he : g.eligible (g.rootWidth/B^2) (w/(T top).length) (ShiftedBlocks.endpoint σ j))
    (sR : ℝ) (hs : g.index (ShiftedBlocks.endpoint σ j) (T top).slope =
      g.index (ShiftedBlocks.endpoint σ j) sR)
    (hblock : g.width (ShiftedBlocks.endpoint σ j) ≤ B*g.width (ShiftedBlocks.endpoint σ (j+1)))
    (b : ℝ) (hb : |b| ≤ w/(g.width (ShiftedBlocks.endpoint σ (j+1))*Real.sqrt (g.branching:ℝ)))
    (z : ℝ × ℝ) :
    let n := fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) (fun t x => (T t).weight Kw D x) σ top x
    let δ := (5*D/Kw)/Real.sqrt (g.branching:ℝ)
    |n (SlopeBox.lineShift sR b z) j-n z j| ≤ Real.exp δ*δ*n z j ∧
      |(n (SlopeBox.lineShift sR b z) j-n (SlopeBox.lineShift sR b z) (j+1))-
        (n z j-n z (j+1))| ≤ Real.exp δ*δ*(n z j-n z (j+1)) := by
  dsimp only
  let slope := fun t => (T t).slope
  let precision := fun t => w/(T t).length
  let cut := g.rootWidth/B^2
  let weight := fun t x => (T t).weight Kw D x
  let lo := ShiftedBlocks.endpoint σ j
  let hi := ShiftedBlocks.endpoint σ (j+1)
  let parent := g.cellTops tops slope precision cut lo (g.index lo (slope top))
  let loss := g.shiftedPathLossTops tops slope precision cut σ top j
  have hp (t : ι) (_ht : t ∈ tops) : 0 ≤ precision t := (div_pos hw (T t).length_pos).le
  have hparent := g.parent_subset_boundary tops slope precision cut 0 lo 0 (slope top)
  have hm (A : Finset ι) (hA : A ⊆ parent) :=
    g.source_submass_relative_motion tops T w B Kw D hw hB hKw hD hwidth
      0 lo lo le_rfl 0 (by norm_num) (g.width_pos lo).le (slope top) sR hs
      (g.width hi) (g.width_pos hi) hblock A (hA.trans hparent) b hb z
  have hn (x : ℝ × ℝ) :
      g.shiftedPathMass tops slope precision cut weight σ top x j = ∑ t ∈ parent, weight t x := by
    rw [shiftedPathMass,ite_eq_left he]
    rfl
  have hl (x : ℝ × ℝ) :=
    g.shiftedPathMass_difference tops slope precision cut weight hp hK σ top j he x
  change |g.shiftedPathMass tops slope precision cut weight σ top (SlopeBox.lineShift sR b z) j-
    g.shiftedPathMass tops slope precision cut weight σ top z j| ≤
      (Real.exp ((5*D/Kw)/Real.sqrt (g.branching:ℝ))*((5*D/Kw)/Real.sqrt (g.branching:ℝ)))*
        g.shiftedPathMass tops slope precision cut weight σ top z j ∧
    |(g.shiftedPathMass tops slope precision cut weight σ top (SlopeBox.lineShift sR b z) j-
      g.shiftedPathMass tops slope precision cut weight σ top (SlopeBox.lineShift sR b z) (j+1))-
      (g.shiftedPathMass tops slope precision cut weight σ top z j-
        g.shiftedPathMass tops slope precision cut weight σ top z (j+1))| ≤
      (Real.exp ((5*D/Kw)/Real.sqrt (g.branching:ℝ))*((5*D/Kw)/Real.sqrt (g.branching:ℝ)))*
        (g.shiftedPathMass tops slope precision cut weight σ top z j-
          g.shiftedPathMass tops slope precision cut weight σ top z (j+1))
  constructor
  · simpa only [hn] using hm parent (Finset.Subset.refl _)
  · simpa only [hl] using hm loss (g.shiftedPathLossTops_subset tops slope precision cut σ top j)

/-- Every pair of physical points in one reference cell has the above
motion bound. This is uniform over cells and their position on the line. -/
theorem source_shifted_line_cell_motion {ι : Type*} {K : ℕ}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B Kw D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hKw : 0 < Kw) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    (hK : 0 < K) (σ : Fin K) (j : ℕ) (top : ι)
    (he : g.eligible (g.rootWidth/B^2) (w/(T top).length) (ShiftedBlocks.endpoint σ j))
    (sR y : ℝ) (hs : g.index (ShiftedBlocks.endpoint σ j) (T top).slope =
      g.index (ShiftedBlocks.endpoint σ j) sR)
    (hblock : g.width (ShiftedBlocks.endpoint σ j) ≤ B*g.width (ShiftedBlocks.endpoint σ (j+1)))
    (grid : FiniteLineGrid)
    (hgrid : grid.width ≤ w/(g.width (ShiftedBlocks.endpoint σ (j+1))*Real.sqrt (g.branching:ℝ)))
    (x z : ℝ) (hx : x ∈ grid.root) (hz : z ∈ grid.root) :
    let n := fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) (fun t x => (T t).weight Kw D x)
      σ top (x,y+sR*x)
    let q := Real.exp ((5*D/Kw)/Real.sqrt (g.branching:ℝ))*
      ((5*D/Kw)/Real.sqrt (g.branching:ℝ))
    n x j ≤ (1+q)*n z j ∧
      n x j-n x (j+1) ≤ (1+q)*(n z j-n z (j+1)) := by
  have hb := (grid.snapshot_displacement_le_width hz hx).trans hgrid
  have hm := g.source_shifted_absolute_motion tops T w B Kw D hw hB hKw hD hwidth
    hK σ j top he sR hs hblock (x-z) hb (z,y+sR*z)
  rw [lineShift_snapshot] at hm
  dsimp only
  constructor
  · have h := (abs_le.mp hm.1).2
    linarith
  · have h := (abs_le.mp hm.2).2
    linarith

end LipschitzHilbert.AngularGrid

end

end OAI
