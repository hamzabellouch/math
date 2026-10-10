import OAI.Analysis.LipschitzHilbert.Trees.SourceReverseCellMarking

namespace OAI

/-! The literal marks along each spatial path provide the active/drop
and unique-exception hypotheses used by the stopped product theorem. -/

noncomputable section
open Set Filter
open scoped Topology
namespace LipschitzHilbert.AngularGrid

theorem eventually_source_stopped_marking (D A_M : ℝ)
    (hD : 0 ≤ D) (hAM : 0 ≤ A_M) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (ι : Type) (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
      (w Kw : ℝ) (hw : 0 < w), 1 ≤ Kw →
      (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
    ∀ (hK : 0 < SourceParameters.blockCount L) (tag : Fin (SourceParameters.blockCount L))
      (top : ι) (origin y : ℝ),
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let count := g.firstIneligibleShiftedBlock cut (w/(T top).length)
      (div_pos hw (T top).length_pos) hK tag
    let grid := sourceReverseLineGrid g L origin hw tag count
    let n := fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) cut (fun t z => (T t).weight Kw D z)
      tag top (x,y+(T top).slope*x)
    ∀ x ∈ grid.root,
    let marked := fun j => sourceMarkedCell
      (grid.cell (ShiftedBlocks.reverseLevel tag count (ShiftedBlocks.reverseIndex count j))
        (grid.index (ShiftedBlocks.reverseLevel tag count (ShiftedBlocks.reverseIndex count j)) x).val)
      (fun z => n z j) (fun z => n z j-n z (j+1)) (L^A_M)
    (∀ j < count, marked j → L^A_M < n x j ∧ (1/4:ℝ) ≤ n x j-n x (j+1)) ∧
    (∀ j < count, ¬marked j → 1 ≤ n x j-n x (j+1) →
      n x j ≤ L^A_M+1 ∧ n x (j+1) ≤ L^A_M) := by
  filter_upwards [eventually_source_reverse_cell_marking D A_M hD hAM] with L hmark
  intro ι g tops T w Kw hw hKw hbranch hwidth hK tag top origin y
  dsimp only
  let cut := g.rootWidth/(SourceParameters.branching L)^2
  let count := g.firstIneligibleShiftedBlock cut (w/(T top).length)
    (div_pos hw (T top).length_pos) hK tag
  let grid := sourceReverseLineGrid g L origin hw tag count
  intro x hx
  have hb (j : ℕ) (hj : j < count) := hmark ι g tops T w Kw hw hKw hbranch hwidth
    hK tag top origin y j hj
  have hc (j : ℕ) : x ∈ grid.cell
      (ShiftedBlocks.reverseLevel tag count (ShiftedBlocks.reverseIndex count j))
      (grid.index (ShiftedBlocks.reverseLevel tag count (ShiftedBlocks.reverseIndex count j)) x).val :=
    (grid.index_eq_iff_mem_cell (ShiftedBlocks.reverseLevel_le tag count _) hx _).mp rfl
  constructor
  · intro j hj hm
    exact (hb j hj _ x (hc j)).1 hm
  · intro j hj hm hd
    exact ⟨((hb j hj _ x (hc j)).2 hm hd).1.le,
      ((hb j hj _ x (hc j)).2 hm hd).2.le⟩

end LipschitzHilbert.AngularGrid

end

end OAI
