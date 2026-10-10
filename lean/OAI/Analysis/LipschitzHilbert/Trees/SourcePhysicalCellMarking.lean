import OAI.Analysis.LipschitzHilbert.Trees.SourceShiftedCellMotion
import OAI.Analysis.LipschitzHilbert.Trees.SourceMarkingParameters
import OAI.Analysis.LipschitzHilbert.Trees.SourceShiftedScales

namespace OAI

/-! The source marking dichotomy for actual top weights on an arbitrary
reference-line cell of the prescribed block length. -/

noncomputable section
open Set Filter
open scoped Topology
namespace LipschitzHilbert.AngularGrid

theorem eventually_source_physical_cell_marking (D A_M : ℝ)
    (hD : 0 ≤ D) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (ι : Type) (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
      (w Kw : ℝ), 0 < w → 1 ≤ Kw →
      (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
    ∀ (_hK : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L))
      (j : ℕ) (top : ι),
      g.eligible (g.rootWidth/(SourceParameters.branching L)^2) (w/(T top).length)
        (ShiftedBlocks.endpoint σ j) →
    ∀ (y : ℝ) (grid : FiniteLineGrid),
      grid.width ≤ sourceLineScale g L w (ShiftedBlocks.endpoint σ (j+1)) →
    let n := fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/(SourceParameters.branching L)^2)
      (fun t z => (T t).weight Kw D z) σ top (x,y+(T top).slope*x)
    let mark := sourceMarkedCell grid.root (fun x => n x j)
      (fun x => n x j-n x (j+1)) (L^A_M)
    ∀ x ∈ grid.root,
      (mark → L^A_M < n x j ∧ (1/4:ℝ) ≤ n x j-n x (j+1)) ∧
      (¬mark → 1 ≤ n x j-n x (j+1) → n x j < L^A_M+1 ∧ n x (j+1) < L^A_M) := by
  filter_upwards [eventually_source_marking_parameters_uniform D A_M hD hAM]
    with L hnumeric
  intro ι g tops T w Kw hw hKw hbranch hwidth hK σ j top he y grid hgrid
  dsimp only
  intro x hx
  let q := Real.exp ((5*D/Kw)/Real.sqrt (SourceParameters.step L))*
    ((5*D/Kw)/Real.sqrt (SourceParameters.step L))
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hnum := hnumeric Kw hKw
  apply source_cell_marking_cases grid.root
    (fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/(SourceParameters.branching L)^2)
      (fun t z => (T t).weight Kw D z) σ top (x,y+(T top).slope*x) j)
    (fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/(SourceParameters.branching L)^2)
      (fun t z => (T t).weight Kw D z) σ top (x,y+(T top).slope*x) (j+1))
    (L^A_M) q
  · intro z _
    exact g.shiftedPathMass_nonneg tops _ _ _ _
      (fun t z => ((T t).weight_pos (zero_lt_one.trans_le hKw) D z).le) σ top _ j
  · exact hq0
  · exact hnum.1.trans (by norm_num)
  · exact hnum.2
  · intro a ha b hb
    have hB : 1 ≤ SourceParameters.branching L :=
      one_le_pow₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
    have hg : grid.width ≤ w/(g.width (ShiftedBlocks.endpoint σ (j+1))*
        Real.sqrt (g.branching:ℝ)) := by
      simpa only [sourceLineScale,hbranch,Real.sqrt_eq_rpow] using hgrid
    have hm := g.source_shifted_line_cell_motion tops T w (SourceParameters.branching L)
      Kw D hw hB (zero_lt_one.trans_le hKw) hD hwidth hK σ j top he
      (T top).slope y rfl (g.source_shifted_width_bounds L hbranch hK σ j).2
      grid hg a b ha hb
    simpa only [hbranch] using hm
  · exact hx

end LipschitzHilbert.AngularGrid

end

end OAI
