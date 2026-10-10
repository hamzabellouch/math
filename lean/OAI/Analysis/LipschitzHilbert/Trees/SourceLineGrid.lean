import OAI.Analysis.LipschitzHilbert.Phase.SourceGridPrediction
import OAI.Analysis.LipschitzHilbert.Trees.LineGridPrimitive

namespace OAI

/-! The actual nested line grid with the rounded manuscript step. A single
refinement has mesh H/G, small enough to retain the G^(-1/16) error when
the carrier spread times H is at most G^(15/16). -/

noncomputable section
namespace LipschitzHilbert

def sourceLineGrid (L origin width : ℝ) (depth : ℕ) (hwidth : 0 < width) : FiniteLineGrid where
  branching := 2^SourceParameters.stepExponent L
  branching_pos := pow_pos (by norm_num) _
  origin := origin
  width := width
  width_pos := hwidth
  depth := depth

theorem sourceLineGrid_mesh (L origin width : ℝ) (depth level : ℕ) (hwidth : 0 < width) :
    (sourceLineGrid L origin width depth hwidth).meshWidth level =
      width/(SourceParameters.step L)^level := by
  simp only [FiniteLineGrid.meshWidth,sourceLineGrid,SourceParameters.step,Nat.cast_pow,Nat.cast_ofNat]

theorem sourceLineGrid_mesh_carrier (L origin width B : ℝ) (depth : ℕ)
    (hwidth : 0 < width) (hspread : B*width ≤ SourceParameters.step L^(15/16:ℝ)) :
    B*(sourceLineGrid L origin width depth hwidth).meshWidth 1 ≤
      SourceParameters.step L^(-(1/16:ℝ)) := by
  have hG := SourceParameters.step_pos L
  rw [sourceLineGrid_mesh,pow_one,← mul_div_assoc]
  apply (div_le_iff₀ hG).mpr
  calc
    _ ≤ SourceParameters.step L^(15/16:ℝ) := hspread
    _ = SourceParameters.step L^(-(1/16:ℝ))*SourceParameters.step L := by
      simpa only [show -(1/16:ℝ)+1 = 15/16 by norm_num,Real.rpow_one] using
        (Real.rpow_add hG (-(1/16:ℝ)) 1)

theorem source_prediction_error_le (C G p K B h : ℝ)
    (hp : 0 ≤ p) (hK : 0 ≤ K) (hmesh : B*h ≤ G^(-(1/16:ℝ))) :
    4*C*G^(-(1/16:ℝ))*p*K+p*B*K*h ≤
      (4*C+1)*G^(-(1/16:ℝ))*p*K := by
  have hm := mul_le_mul_of_nonneg_left hmesh (mul_nonneg hp hK)
  calc
    _ = 4*C*G^(-(1/16:ℝ))*p*K+(p*K)*(B*h) := by ring
    _ ≤ 4*C*G^(-(1/16:ℝ))*p*K+(p*K)*G^(-(1/16:ℝ)) := add_le_add_right hm _
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
