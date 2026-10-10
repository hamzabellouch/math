import OAI.Analysis.LipschitzHilbert.Trees.SourceReverseBlocks
import OAI.Analysis.LipschitzHilbert.Trees.SourceSnapshotWindow

namespace OAI

/-! The local grid used by physical packet prediction is exactly a translated
window of the single reverse angular grid. No replacement partition or
rounding of a block length is required. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

namespace FiniteLineGrid

private theorem eq_of_fields (g h : FiniteLineGrid)
    (hb : g.branching = h.branching) (ho : g.origin = h.origin)
    (hw : g.width = h.width) (hd : g.depth = h.depth) : g = h := by
  cases g
  cases h
  simp_all

/-- A displacement-coordinate predictor gives the same bound on the
physical reference line and keeps its exact probability average. -/
theorem snapshot_prediction_transfer (g : FiniteLineGrid) (x₀ y s ε : ℝ)
    (level : ℕ) (beta : ℝ × ℝ → ℝ) (P : ℝ → ℝ)
    (hP : Measurable P)
    (hint : Integrable P (intervalProbability (g.atSnapshot x₀).origin
      ((g.atSnapshot x₀).origin+(g.atSnapshot x₀).width)))
    (hpos : ∀ b, 0 ≤ P b)
    (havg : (∫ b, P b ∂intervalProbability (g.atSnapshot x₀).origin
      ((g.atSnapshot x₀).origin+(g.atSnapshot x₀).width)) ≤ 1)
    (hconst : ∀ b c, (g.atSnapshot x₀).index level b =
      (g.atSnapshot x₀).index level c → P b = P c)
    (hcompare : ∀ b ∈ (g.atSnapshot x₀).root,
      beta (SlopeBox.lineShift s b (x₀,y+s*x₀)) ≤ Real.exp ε*P b) :
    ∃ F : ℝ → ℝ, Measurable F ∧
      Integrable F (intervalProbability g.origin (g.origin+g.width)) ∧
      (∀ x, 0 ≤ F x) ∧
      (∫ x, F x ∂intervalProbability g.origin (g.origin+g.width)) ≤ 1 ∧
      (∀ x z, g.index level x = g.index level z → F x = F z) ∧
      ∀ x ∈ g.root, beta (x,y+s*x) ≤ Real.exp ε*F x := by
  obtain ⟨hm,hi,hp,ha,hc⟩ := g.snapshot_factor_transfer x₀ level P hP hint hpos havg hconst
  refine ⟨fun x => P (x-x₀),hm,hi,hp,ha,hc,?_⟩
  intro x hx
  have he := hcompare (x-x₀) ((g.atSnapshot_mem_root x₀ x).mpr hx)
  simpa only [lineShift_snapshot] using he

end FiniteLineGrid

/-- The physical block predictor uses this very translated reverse-grid
window, including the shorter initial angular block. -/
theorem source_reverse_snapshot_window {K : ℕ} (g : AngularGrid) (L origin : ℝ)
    {w : ℝ} (hw : 0 < w) (σ : Fin K) (hK : 0 < K) {count j : ℕ}
    (hj : j < count) (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (i : ℕ) (x₀ : ℝ) :
    let grid := sourceReverseLineGrid g L origin hw σ count
    let coarse := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j)
    let fine := ShiftedBlocks.reverseLevel σ count (ShiftedBlocks.reverseIndex count j+1)
    (grid.lineWindow coarse i (fine-coarse)).atSnapshot x₀ =
      sourceLineGrid L ((grid.lineWindow coarse i (fine-coarse)).origin-x₀)
        (sourceLineScale g L w (ShiftedBlocks.endpoint σ (j+1)))
        (ShiftedBlocks.endpoint σ (j+1)-ShiftedBlocks.endpoint σ j)
        (sourceLineScale_pos g L hw (ShiftedBlocks.endpoint σ (j+1))) := by
  dsimp only
  apply FiniteLineGrid.eq_of_fields
  · rfl
  · rfl
  · exact (source_reverse_local_mesh g L origin hw σ hK hj hbranch i).1
  · exact ShiftedBlocks.reverseLevel_block_length hK σ hj

end LipschitzHilbert

end

end OAI
