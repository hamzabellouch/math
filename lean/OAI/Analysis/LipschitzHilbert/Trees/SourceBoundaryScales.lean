import OAI.Analysis.LipschitzHilbert.Trees.SourceShiftedScales
import OAI.Analysis.LipschitzHilbert.Trees.SourceBlockModulus

namespace OAI

/-! The manuscript's boundary radius is G^(-1/4) times the parent width.
At a last transition this is exactly G^(3/4) times the child width. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid

def sourceBoundaryGap (g : AngularGrid) (L : ℝ) (level : ℕ) : ℝ :=
  SourceParameters.step L^(-(1/4:ℝ))*g.width level

theorem sourceBoundaryGap_pos (g : AngularGrid) (L : ℝ) (level : ℕ) :
    0 < g.sourceBoundaryGap L level :=
  mul_pos (Real.rpow_pos_of_pos (SourceParameters.step_pos L) _) (g.width_pos level)

theorem sourceBoundaryGap_le_width (g : AngularGrid) (L : ℝ) {h level : ℕ}
    (hle : h ≤ level) : g.sourceBoundaryGap L level ≤ g.width h := by
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  exact (mul_le_of_le_one_left (g.width_pos level).le
    (Real.rpow_le_one_of_one_le_of_nonpos hG (by norm_num))).trans (g.width_antitone hle)

theorem sourceBoundaryGap_eq_sourceGap (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L) (level : ℕ) :
    g.sourceBoundaryGap L level = g.sourceGap L (level+1) := by
  have hw := g.source_width_ratio L (Nat.le_succ level) hbranch
  change g.width level = SourceParameters.step L^((level+1)-level)*g.width (level+1) at hw
  simp only [Nat.add_sub_cancel_left,pow_one] at hw
  have hp : SourceParameters.step L^(-(1/4:ℝ))*SourceParameters.step L =
      SourceParameters.step L^(3/4:ℝ) := by
    calc
      _ = SourceParameters.step L^(-(1/4:ℝ))*SourceParameters.step L^(1:ℝ) := by
        rw [Real.rpow_one]
      _ = SourceParameters.step L^(-(1/4:ℝ)+1) :=
        (Real.rpow_add (SourceParameters.step_pos L) _ _).symm
      _ = _ := by norm_num
  rw [sourceBoundaryGap,hw,← mul_assoc,hp]
  rfl

/-- The boundary mass in the shared analytic family is exactly the
neighborhood mass used in the shifted block's graph predictor. -/
theorem source_shifted_boundary_mass {ι X : Type*}
    (g : AngularGrid) (L : ℝ) (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (tops : Finset ι) (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hK : 0 < SourceParameters.blockCount L) (σ : Fin (SourceParameters.blockCount L))
    (j : ℕ) (s : ℝ) (x : X) :
    g.sourceBoundaryMass tops slope precision cutoff weight (SourceParameters.blockCount L)
      (g.sourceBoundaryGap L) (ShiftedBlocks.lastTransition σ j)
      (g.index (ShiftedBlocks.endpoint σ (j+1)) s) x =
    g.boundaryMass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ j)
      (ShiftedBlocks.lastTransition σ j) (g.sourceGap L (ShiftedBlocks.endpoint σ (j+1))) s x := by
  rw [← ShiftedBlocks.lastTransition_succ σ j,
    g.sourceBoundaryMass_path tops slope precision cutoff weight hK,
    ← ShiftedBlocks.endpoint_eq_last_sub σ j,
    g.sourceBoundaryGap_eq_sourceGap L hbranch,ShiftedBlocks.lastTransition_succ]

end LipschitzHilbert.AngularGrid

end

end OAI
