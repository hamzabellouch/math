import OAI.Analysis.LipschitzHilbert.Trees.SourceDensityKeepers

namespace OAI

/-! Spatial part of the selected-tree packing argument. Boxes are compared
in a common direction before passing to the selecting top's coordinates. -/
noncomputable section
open Set
namespace LipschitzHilbert

theorem common_direction_center_bounds (x y x' y' t ell r W K : ℝ)
    (hell : ell ≤ r) (hK : 0 ≤ K) (z : ℝ×ℝ)
    (hx : |z.1-x| ≤ K*ell) (hy : |(z.2-y)-t*(z.1-x)| ≤ K*W)
    (hx' : |z.1-x'| ≤ K*r) (hy' : |(z.2-y')-t*(z.1-x')| ≤ K*W) :
    |x-x'| ≤ 2*K*r ∧ |(y-y')-t*(x-x')| ≤ 2*K*W := by
  constructor
  · calc
      _ = |(z.1-x')-(z.1-x)| := by congr 1; ring
      _ ≤ |z.1-x'|+|z.1-x| := abs_sub _ _
      _ ≤ K*r+K*ell := add_le_add hx' hx
      _ ≤ 2*K*r := by nlinarith only [mul_le_mul_of_nonneg_left hell hK]
  · calc
      _ = |((z.2-y')-t*(z.1-x'))-((z.2-y)-t*(z.1-x))| := by congr 1; ring
      _ ≤ |(z.2-y')-t*(z.1-x')|+|(z.2-y)-t*(z.1-x)| := abs_sub _ _
      _ ≤ K*W+K*W := add_le_add hy' hy
      _ = _ := by ring

theorem center_in_enlarged_selecting_top (T : SlopeBox)
    (x y x' y' t r W K C A : ℝ)
    (hW : 0 < W) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hlen : r ≤ T.length) (hwidth : T.width=W)
    (hcenter : (x',y') ∈ densitySpatialBox T (1/2))
    (hx : |x-x'| ≤ 2*K*r)
    (hy : |(y-y')-t*(x-x')| ≤ 2*K*W)
    (hangle : |T.slope-t| * r ≤ C*W)
    (hA : 2*K*(1+C)+1/2 ≤ A) :
    (x,y) ∈ densitySpatialBox T A := by
  have hA' : 2*K+1/2 ≤ A := by nlinarith only [hA,mul_nonneg hK hC]
  refine ⟨?_,?_⟩
  · calc
      _ ≤ |x-x'|+|x'-T.x| := abs_sub_le _ _ _
      _ ≤ 2*K*r+(1/2)*T.length := add_le_add hx hcenter.1
      _ ≤ (2*K+1/2)*T.length := by
        nlinarith only [mul_le_mul_of_nonneg_left hlen (mul_nonneg (by norm_num : (0:ℝ)≤2) hK)]
      _ ≤ _ := mul_le_mul_of_nonneg_right hA' T.length_pos.le
  · have hchange : |(T.slope-t)*(x-x')| ≤ 2*K*C*W := by
      rw [abs_mul]
      calc
        _ ≤ |T.slope-t| * (2*K*r) := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
        _ = 2*K*(|T.slope-t| * r) := by ring
        _ ≤ 2*K*(C*W) := mul_le_mul_of_nonneg_left hangle (mul_nonneg (by norm_num) hK)
        _ = _ := by ring
    calc
      _ = |((y-y')-t*(x-x'))-((T.slope-t)*(x-x'))+
          ((y'-T.y)-T.slope*(x'-T.x))| := by congr 1; ring
      _ ≤ |(y-y')-t*(x-x')|+|(T.slope-t)*(x-x')|+
          |(y'-T.y)-T.slope*(x'-T.x)| := (abs_add_le _ _).trans
        (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ 2*K*W+2*K*C*W+(1/2)*W :=
        add_le_add (add_le_add hy hchange) (by simpa only [hwidth] using hcenter.2)
      _ = (2*K*(1+C)+1/2)*W := by ring
      _ ≤ A*T.width := by rw [hwidth]; exact mul_le_mul_of_nonneg_right hA hW.le

end LipschitzHilbert

end

end OAI
