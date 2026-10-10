import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalCellMarking
import OAI.Analysis.LipschitzHilbert.Trees.SourceTerminalScale

namespace OAI

/-! The literal source marking rule on every nested reverse-grid cell.
Eligibility is derived from the actual first terminal block. -/

noncomputable section
open Set Filter
open scoped Topology
namespace LipschitzHilbert.AngularGrid

theorem eventually_source_reverse_cell_marking (D A_M : ℝ)
    (hD : 0 ≤ D) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (ι : Type) (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
      (w Kw : ℝ) (hw : 0 < w), 1 ≤ Kw →
      (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
    ∀ (hK : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L))
      (top : ι) (origin y : ℝ),
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let count := g.firstIneligibleShiftedBlock cut (w/(T top).length)
      (div_pos hw (T top).length_pos) hK σ
    let grid := sourceReverseLineGrid g L origin hw σ count
    let n := fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) cut (fun t z => (T t).weight Kw D z)
      σ top (x,y+(T top).slope*x)
    ∀ j < count, ∀ i : ℕ,
    let coarse := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)
    let mark := sourceMarkedCell (grid.cell coarse i) (fun x => n x j)
      (fun x => n x j-n x (j+1)) (L^A_M)
    ∀ x ∈ grid.cell coarse i,
      (mark → L^A_M < n x j ∧ (1/4:ℝ) ≤ n x j-n x (j+1)) ∧
      (¬mark → 1 ≤ n x j-n x (j+1) → n x j < L^A_M+1 ∧ n x (j+1) < L^A_M) := by
  filter_upwards [eventually_source_physical_cell_marking D A_M hD hAM]
    with L hmark
  intro ι g tops T w Kw hw hKw hbranch hwidth hK σ top origin y
  dsimp only
  let cut := g.rootWidth/(SourceParameters.branching L)^2
  let count := g.firstIneligibleShiftedBlock cut (w/(T top).length)
    (div_pos hw (T top).length_pos) hK σ
  let grid := sourceReverseLineGrid g L origin hw σ count
  intro j hj i x hx
  let coarse := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)
  let fine := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j+1)
  have he := g.eligible_before_firstIneligibleShiftedBlock cut (w/(T top).length)
    (div_pos hw (T top).length_pos) hK σ hj
  have hwgrid : (grid.lineWindow coarse i (fine-coarse)).width ≤
      sourceLineScale g L w (ShiftedBlocks.endpoint σ (j+1)) :=
    (source_reverse_local_mesh g L origin hw σ hK hj hbranch i).1.le
  have hxgrid : x ∈ (grid.lineWindow coarse i (fine-coarse)).root := by
    rwa [FiniteLineGrid.lineWindow_root]
  have hm := hmark ι g tops T w Kw hw hKw hbranch hwidth hK σ j top he y
    (grid.lineWindow coarse i (fine-coarse)) hwgrid x hxgrid
  simpa only [FiniteLineGrid.lineWindow_root] using hm

end LipschitzHilbert.AngularGrid

end

end OAI
