import OAI.Analysis.LipschitzHilbert.Trees.SourceLineGrid
import OAI.Analysis.LipschitzHilbert.Phase.AngularGeometry

namespace OAI

/-! The source line scales for a whole angular block. Refinement from the
child scale to the parent scale cancels the angular branching exactly. -/

noncomputable section
namespace LipschitzHilbert

/-- The manuscript line-window length at one angular generation. -/
def sourceLineScale (g : AngularGrid) (L w : ℝ) (level : ℕ) : ℝ :=
  w / (g.width level * SourceParameters.step L ^ (1/2 : ℝ))

theorem sourceLineScale_pos (g : AngularGrid) (L : ℝ) {w : ℝ}
    (hw : 0 < w) (level : ℕ) : 0 < sourceLineScale g L w level := by
  unfold sourceLineScale
  exact div_pos hw (mul_pos (g.width_pos level)
    (Real.rpow_pos_of_pos (SourceParameters.step_pos L) _))

theorem source_block_line_mesh (g : AngularGrid) (L origin : ℝ) {w : ℝ}
    (hw : 0 < w) (lower start : ℕ) (hle : lower ≤ start)
    (hbranch : (g.branching : ℝ) = SourceParameters.step L) :
    (sourceLineGrid L origin (sourceLineScale g L w start) (start-lower)
      (sourceLineScale_pos g L hw start)).meshWidth (start-lower) =
      sourceLineScale g L w lower := by
  rw [sourceLineGrid_mesh]
  have hG := SourceParameters.step_pos L
  have hpow : SourceParameters.step L ^ start =
      SourceParameters.step L ^ lower * SourceParameters.step L ^ (start-lower) := by
    rw [← pow_add, Nat.add_sub_of_le hle]
  unfold sourceLineScale AngularGrid.width
  rw [hbranch, hpow]
  field_simp

theorem source_block_line_carrier (g : AngularGrid) (L origin : ℝ) {w F C : ℝ}
    (hw : 0 < w) (lower start : ℕ) (hle : lower ≤ start)
    (hbranch : (g.branching : ℝ) = SourceParameters.step L)
    (hF : F ≤ C*g.width lower/w) :
    F*(sourceLineGrid L origin (sourceLineScale g L w start) (start-lower)
      (sourceLineScale_pos g L hw start)).meshWidth (start-lower) ≤
      C*SourceParameters.step L^(-(1/2:ℝ)) := by
  rw [source_block_line_mesh g L origin hw lower start hle hbranch]
  calc
    _ ≤ (C*g.width lower/w)*sourceLineScale g L w lower :=
      mul_le_mul_of_nonneg_right hF (sourceLineScale_pos g L hw lower).le
    _ = C*SourceParameters.step L^(-(1/2:ℝ)) := by
      rw [Real.rpow_neg (SourceParameters.step_pos L).le]
      unfold sourceLineScale
      field_simp [(g.width_pos lower).ne']

/-- At the source window size, the angular gap times the transverse
frequency clears the exact Fourier threshold used by near-uniform averaging. -/
theorem source_line_fourier_threshold (g : AngularGrid) (L : ℝ)
    {w c0 : ℝ} (hw : 0 < w) (level : ℕ)
    (hc0 : SourceParameters.step L^(-(1/8:ℝ)) ≤ c0) :
    1/(sourceLineScale g L w level*SourceParameters.step L^(-(1/8:ℝ))) ≤
      (SourceParameters.step L^(3/4:ℝ)*g.width level)*(c0/w) := by
  have hG := SourceParameters.step_pos L
  have hwidth := g.width_pos level
  have hpow : SourceParameters.step L^(3/4:ℝ)*SourceParameters.step L^(-(1/8:ℝ)) =
      SourceParameters.step L^(1/2:ℝ)/SourceParameters.step L^(-(1/8:ℝ)) := by
    rw [← Real.rpow_add hG, ← Real.rpow_sub hG]
    norm_num
  calc
    _ = (SourceParameters.step L^(3/4:ℝ)*g.width level)*
        (SourceParameters.step L^(-(1/8:ℝ))/w) := by
      unfold sourceLineScale
      calc
        _ = (g.width level/w)*(SourceParameters.step L^(1/2:ℝ)/
            SourceParameters.step L^(-(1/8:ℝ))) := by
          field_simp
        _ = (g.width level/w)*(SourceParameters.step L^(3/4:ℝ)*
            SourceParameters.step L^(-(1/8:ℝ))) := by rw [hpow]
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hc0 hw.le)
      (mul_pos (Real.rpow_pos_of_pos hG _) hwidth).le

end LipschitzHilbert

end

end OAI
