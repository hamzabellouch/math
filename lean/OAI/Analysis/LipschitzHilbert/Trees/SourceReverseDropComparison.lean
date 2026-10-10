import OAI.Analysis.LipschitzHilbert.Trees.SourceReverseCellMarking

namespace OAI

/-! Actual path-drop comparison between any two points of one reverse
line cell. This supplies the snapshot-to-point error transfer used when
patching the physical predictors. -/

noncomputable section
open Set Filter
open scoped Topology
namespace LipschitzHilbert.AngularGrid

theorem eventually_source_reverse_drop_comparison (D : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (ι : Type) (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
      (w Kw : ℝ) (hw : 0 < w), 1 ≤ Kw →
      (g.branching:ℝ) = SourceParameters.step L →
      (∀ t ∈ tops, (SourceParameters.branching L)^2*w ≤ (T t).width) →
    ∀ (hK : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L))
      (top : ι), top ∈ tops → ∀ origin y : ℝ,
    let cut := g.rootWidth/(SourceParameters.branching L)^2
    let count := g.firstIneligibleShiftedBlock cut (w/(T top).length)
      (div_pos hw (T top).length_pos) hK σ
    let grid := sourceReverseLineGrid g L origin hw σ count
    let n := fun x => g.shiftedPathMass tops (fun t => (T t).slope)
      (fun t => w/(T t).length) cut (fun t z => (T t).weight Kw D z)
      σ top (x,y+(T top).slope*x)
    ∀ j < count, ∀ i : ℕ,
    let coarse := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)
    ∀ x ∈ grid.cell coarse i, ∀ z ∈ grid.cell coarse i,
      pathDrop (n z) j/2 ≤ pathDrop (n x) j ∧
        pathDrop (n x) j ≤ 2*pathDrop (n z) j := by
  filter_upwards [eventually_source_marking_parameters_uniform D 0 hD (by norm_num)]
    with L hnumeric
  intro ι g tops T w Kw hw hKw hbranch hwidth hK σ top htop origin y
  dsimp only
  let cut := g.rootWidth/(SourceParameters.branching L)^2
  let count := g.firstIneligibleShiftedBlock cut (w/(T top).length)
    (div_pos hw (T top).length_pos) hK σ
  let grid := sourceReverseLineGrid g L origin hw σ count
  intro j hj i x hx z hz
  let coarse := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)
  let fine := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j+1)
  let win := grid.lineWindow coarse i (fine-coarse)
  have hxw : x ∈ win.root := by
    change x ∈ (grid.lineWindow coarse i (fine-coarse)).root
    rwa [FiniteLineGrid.lineWindow_root]
  have hzw : z ∈ win.root := by
    change z ∈ (grid.lineWindow coarse i (fine-coarse)).root
    rwa [FiniteLineGrid.lineWindow_root]
  have hb : |x-z| ≤ w/(g.width (ShiftedBlocks.endpoint σ (j+1))*Real.sqrt (g.branching:ℝ)) := by
    have h := win.snapshot_displacement_le_width hzw hxw
    have hwid := (source_reverse_local_mesh g L origin hw σ hK hj hbranch i).1
    change win.width = sourceLineScale g L w (ShiftedBlocks.endpoint σ (j+1)) at hwid
    rw [hwid] at h
    simpa only [sourceLineScale,hbranch,Real.sqrt_eq_rpow] using h
  have he := g.eligible_before_firstIneligibleShiftedBlock cut (w/(T top).length)
    (div_pos hw (T top).length_pos) hK σ hj
  have hB : 1 ≤ SourceParameters.branching L :=
    one_le_pow₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hsmall : Real.exp ((5*D/Kw)/Real.sqrt (g.branching:ℝ))*
      ((5*D/Kw)/Real.sqrt (g.branching:ℝ)) ≤ 1/8 := by
    simpa only [hbranch] using (hnumeric Kw hKw).1
  have hm := g.source_shifted_path_drop_motion tops T w (SourceParameters.branching L)
    Kw D hw hB (zero_lt_one.trans_le hKw) hD hwidth hK σ j top htop he
    (ShiftedBlocks.endpoint σ j) le_rfl (T top).slope rfl
    (g.source_shifted_width_bounds L hbranch hK σ j).2 (x-z) hb
    (z,y+(T top).slope*z) hsmall
  rw [lineShift_snapshot] at hm
  exact ⟨hm.2.2.1,hm.2.2.2⟩

end LipschitzHilbert.AngularGrid

end

end OAI
