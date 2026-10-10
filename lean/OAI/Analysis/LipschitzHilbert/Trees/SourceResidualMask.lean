import OAI.Analysis.LipschitzHilbert.Trees.SourceMaskTail

namespace OAI

/-! The mask in §4 is dominated by the actual hierarchy weight with
dilation `L^(A+2)`. Consequently the negative weight power in every
residual coefficient costs at most one, uniformly in the spatial point. -/

noncomputable section
namespace LipschitzHilbert

theorem topSincMask_abs_le_one (L A x y : ℝ) : |topSincMask L A x y| ≤ 1 := by
  simpa only [abs_of_nonneg (topSincMask_nonneg L A x y)] using
    topSincMask_le_one L A x y

theorem topSincMask_radial_power {L A x y : ℝ} (hL : 2 ≤ L)
    (hfar : L^(A+2) ≤ |x|+|y|) :
    |topSincMask L A x y| ≤ (L^(A+2)/(|x|+|y|))^(2*⌈L⌉₊) := by
  have hL0 : 0 < L := by linarith
  have hs : 0 < L^A := Real.rpow_pos_of_pos hL0 _
  have hK : 0 < L^(A+2) := Real.rpow_pos_of_pos hL0 _
  have hr : 0 < |x|+|y| := hK.trans_le hfar
  have hscale : 2*L^A ≤ L^(A+2) := by
    rw [Real.rpow_add hL0,Real.rpow_two]
    nlinarith [sq_nonneg (L-2)]
  have hcoord : (|x|+|y|)/2 ≤ |x| ∨ (|x|+|y|)/2 ≤ |y| := by
    by_contra h
    push Not at h
    linarith
  have hh : 0 < (|x|+|y|)/(2*L^A) := by positivity
  have hproduct : |Real.sinc (x/L^A)*Real.sinc (y/L^A)| ≤
      L^(A+2)/(|x|+|y|) := by
    have hratio : 1/((|x|+|y|)/(2*L^A)) = (2*L^A)/(|x|+|y|) := by
      field_simp
    have hsmall : |Real.sinc (x/L^A)*Real.sinc (y/L^A)| ≤
        1/((|x|+|y|)/(2*L^A)) := by
      rw [abs_mul]
      rcases hcoord with hx | hy
      · have hxx : (|x|+|y|)/(2*L^A) ≤ |x/L^A| := by
          rw [abs_div,abs_of_pos hs]
          apply (le_div_iff₀ hs).mpr
          calc
            _ = (|x|+|y|)/2 := by field_simp
            _ ≤ _ := hx
        simpa only [mul_one] using mul_le_mul
          (abs_sinc_le_reciprocal_of_large hh hxx) (Real.abs_sinc_le_one (y/L^A))
          (abs_nonneg _) (by positivity : 0 ≤ 1/((|x|+|y|)/(2*L^A)))
      · have hyy : (|x|+|y|)/(2*L^A) ≤ |y/L^A| := by
          rw [abs_div,abs_of_pos hs]
          apply (le_div_iff₀ hs).mpr
          calc
            _ = (|x|+|y|)/2 := by field_simp
            _ ≤ _ := hy
        simpa only [one_mul] using mul_le_mul
          (Real.abs_sinc_le_one (x/L^A)) (abs_sinc_le_reciprocal_of_large hh hyy)
          (abs_nonneg _) zero_le_one
    rw [hratio] at hsmall
    exact hsmall.trans (div_le_div_of_nonneg_right hscale hr.le)
  simpa only [topSincMask,sincProductMask,abs_pow] using
    pow_le_pow_left₀ (abs_nonneg _) hproduct (2*⌈L⌉₊)

theorem topSincMask_le_topShape {L A D x y : ℝ} (hL : 2 ≤ L)
    (hD : 0 ≤ D) (hdegree : D ≤ ((2*⌈L⌉₊:ℕ):ℝ)) :
    |topSincMask L A x y| ≤ topShape (L^(A+2)) D x y := by
  have hL0 : 0 < L := by linarith
  have hK : 0 < L^(A+2) := Real.rpow_pos_of_pos hL0 _
  have hr : 0 ≤ |x|+|y| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hb : 0 < 1+(|x|+|y|)/L^(A+2) := by positivity
  have hshape : topShape (L^(A+2)) D x y =
      (2/(1+(|x|+|y|)/L^(A+2)))^D := by
    unfold topShape
    rw [Real.rpow_neg hb.le,Real.div_rpow (by norm_num : (0:ℝ) ≤ 2) hb.le]
    rfl
  by_cases hfar : L^(A+2) ≤ |x|+|y|
  · have hr0 : 0 < |x|+|y| := hK.trans_le hfar
    have hratio : 0 < L^(A+2)/(|x|+|y|) := div_pos hK hr0
    have hratio1 : L^(A+2)/(|x|+|y|) ≤ 1 := (div_le_one hr0).mpr hfar
    have hbase : L^(A+2)/(|x|+|y|) ≤ 2/(1+(|x|+|y|)/L^(A+2)) := by
      apply (div_le_div_iff₀ hr0 hb).mpr
      have hcancel : L^(A+2)*(1+(|x|+|y|)/L^(A+2)) = L^(A+2)+(|x|+|y|) := by
        field_simp
      rw [hcancel]
      linarith
    calc
      _ ≤ (L^(A+2)/(|x|+|y|))^(2*⌈L⌉₊) := topSincMask_radial_power hL hfar
      _ = (L^(A+2)/(|x|+|y|))^((2*⌈L⌉₊:ℕ):ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (L^(A+2)/(|x|+|y|))^D :=
        Real.rpow_le_rpow_of_exponent_ge hratio hratio1 hdegree
      _ ≤ (2/(1+(|x|+|y|)/L^(A+2)))^D := Real.rpow_le_rpow hratio.le hbase hD
      _ = _ := hshape.symm
  · have hbase : 1 ≤ 2/(1+(|x|+|y|)/L^(A+2)) := by
      apply (le_div_iff₀ hb).mpr
      have h := (div_le_one hK).mpr (not_le.mp hfar).le
      linarith
    exact (topSincMask_abs_le_one L A x y).trans
      (hshape ▸ Real.one_le_rpow hbase hD)

theorem negative_weight_power_mul_le_one {w q a : ℝ} (hw : 0 < w)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hqw : q ≤ w) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    w^(-a)*q ≤ 1 := by
  by_cases hw1 : w ≤ 1
  · have hp : w^(-a) ≤ w^(-1:ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hw hw1 (by linarith)
    calc
      _ ≤ w^(-1:ℝ)*w := mul_le_mul hp hqw hq (Real.rpow_nonneg hw.le _)
      _ = 1 := by rw [Real.rpow_neg_one,inv_mul_cancel₀ hw.ne']
  · have hp : w^(-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
      (not_le.mp hw1).le (neg_nonpos.mpr ha)
    exact (mul_le_mul hp hq1 hq zero_le_one).trans_eq (mul_one 1)

theorem SlopeBox.residual_mask_weight_bound (T : SlopeBox) {L A D a : ℝ}
    (hL : 2 ≤ L) (hD : 0 ≤ D) (hdegree : D ≤ ((2*⌈L⌉₊:ℕ):ℝ))
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (z : ℝ×ℝ) :
    (T.weight (L^(A+2)) D z)^(-a)*|T.mask L A z| ≤ 1 := by
  have hL0 : 0 < L := by linarith
  apply negative_weight_power_mul_le_one (T.weight_pos (Real.rpow_pos_of_pos hL0 _) D z)
    (abs_nonneg _) (topSincMask_abs_le_one L A (T.horizontal z) (T.transverse z))
    _ ha ha1
  exact topSincMask_le_topShape hL hD hdegree

end LipschitzHilbert

end

end OAI
