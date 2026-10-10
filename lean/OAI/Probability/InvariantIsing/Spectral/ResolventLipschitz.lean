import OAI.Probability.InvariantIsing.Spectral.CompactResolventTests

namespace OAI

/-! The exact uniform modulus used when clipping nonnegative spectra. -/
noncomputable section
namespace InvariantIsing

theorem positiveResolventTest_sub_le {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    |positiveResolventTest t x-positiveResolventTest t y| ≤ |x-y|/t^2 := by
  have hx := le_max_right x 0
  have hy := le_max_right y 0
  have htx : 0 < t+max x 0 := add_pos_of_pos_of_nonneg ht hx
  have hty : 0 < t+max y 0 := add_pos_of_pos_of_nonneg ht hy
  have hd : t^2 ≤ (t+max x 0)*(t+max y 0) := by
    nlinarith [mul_nonneg hx hy]
  have hn : |max y 0-max x 0| ≤ |x-y| := by
    simpa only [Real.dist_eq,NNReal.coe_one,one_mul,abs_sub_comm,id_eq] using
      (LipschitzWith.id.max_const (0 : ℝ)).dist_le_mul y x
  have he : positiveResolventTest t x-positiveResolventTest t y =
      (max y 0-max x 0)/((t+max x 0)*(t+max y 0)) := by
    unfold positiveResolventTest
    field_simp [htx.ne',hty.ne']
    ring
  rw [he,abs_div,abs_of_pos (mul_pos htx hty)]
  exact (div_le_div_of_nonneg_right hn (mul_pos htx hty).le).trans
    (div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos ht) hd)

end InvariantIsing

end

end OAI
