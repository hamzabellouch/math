import OAI.Analysis.CircleDomains.Selection.VerticalCylinderCover

namespace OAI

/-! A fixed finite coloring separates the enlarged equal-scale cells.
This supplies bounded overlap without assuming measure doubling. -/
open Set
noncomputable section
namespace CircleDomainRigidity

lemma equal_scale_cell_separation {s : ℝ} (hs : 0 < s) {k l : ℤ} (hkl : k ≠ l)
    (r : ℝ) {x y : ℝ}
    (hx : x ∈ Icc ((16*(k:ℝ)+r)*s) ((16*(k:ℝ)+r+1)*s))
    (hy : y ∈ Icc ((16*(l:ℝ)+r)*s) ((16*(l:ℝ)+r+1)*s)) :
    8*s < |x-y| := by
  rcases lt_or_gt_of_ne hkl with h | h
  · have hi : (k:ℝ)+1 ≤ (l:ℝ) := by exact_mod_cast (show k+1 ≤ l by omega)
    have hm := mul_le_mul_of_nonneg_right hi hs.le
    have hgap : 15*s ≤ y-x := by nlinarith [hx.2,hy.1]
    have he : y-x ≤ |x-y| := by rw [abs_sub_comm]; exact le_abs_self _
    linarith
  · have hi : (l:ℝ)+1 ≤ (k:ℝ) := by exact_mod_cast (show l+1 ≤ k by omega)
    have hm := mul_le_mul_of_nonneg_right hi hs.le
    have hgap : 15*s ≤ x-y := by nlinarith [hy.2,hx.1]
    linarith [le_abs_self (x-y)]

end CircleDomainRigidity

end

end OAI
