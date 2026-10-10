import OAI.Analysis.LipschitzHilbert.Estimates.CountParameters

namespace OAI

/-! Fixed powers supplying the witness dilation and popularity threshold. -/

noncomputable section

namespace LipschitzHilbert

theorem count_witness_dilation {L a k p : ℝ} (hL : 2 ≤ L)
    (ha : a + 1 ≤ p) (hk : k + 1 ≤ p) : L ^ a + L ^ k ≤ L ^ p := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have ha' := Real.rpow_le_rpow_of_exponent_le hL1 (show a ≤ p - 1 by linarith)
  have hk' := Real.rpow_le_rpow_of_exponent_le hL1 (show k ≤ p - 1 by linarith)
  have hp : 0 ≤ L ^ (p - 1) := Real.rpow_nonneg hL0.le _
  have hmul := mul_le_mul_of_nonneg_right hL hp
  have heq : L ^ p = L * L ^ (p - 1) := by
    calc
      L ^ p = L ^ ((p - 1) + 1) := by congr 1; ring
      _ = L ^ (p - 1) * L := Real.rpow_add_one hL0.ne' _
      _ = _ := mul_comm _ _
  rw [heq]
  linarith

/-- One extra power of `L` absorbs the compact-extraction and interval
constants in the popularity average. -/
theorem count_popular_threshold {L a p t : ℝ} (hL : 8 ≤ L)
    (ht : 2 * a + p + 1 ≤ t) :
    L ^ (-t) ≤ L ^ (-a) / (8 * L ^ a * L ^ p) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have ha : 0 < L ^ a := Real.rpow_pos_of_pos hL0 _
  have hp : 0 < L ^ p := Real.rpow_pos_of_pos hL0 _
  have hsmall := Real.rpow_le_rpow_of_exponent_le hL1
    (show -t ≤ -(2 * a + p + 1) by linarith)
  have hid : L ^ (-(2 * a + p + 1)) * (8 * L ^ a * L ^ p) =
      (8 / L) * L ^ (-a) := by
    calc
      _ = 8 * (L ^ (-(2 * a + p + 1)) * L ^ a * L ^ p) := by ring
      _ = 8 * L ^ (-(a + 1)) := by
        rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
        congr 2
        ring
      _ = (8 / L) * L ^ (-a) := by
        have he : -(a + 1) = -a - 1 := by ring
        rw [he, Real.rpow_sub_one hL0.ne']
        ring
  apply hsmall.trans
  apply (le_div_iff₀ (by positivity : 0 < 8 * L ^ a * L ^ p)).mpr
  rw [hid]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hL0.le _) ((div_le_one hL0).mpr hL)

end LipschitzHilbert

end

end OAI
