import OAI.Analysis.CircleDomains.Topology.AnnularCutoffs

namespace OAI

/-! A concrete decreasing sequence of separated transition radii. -/
open Set Function MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 def annularRadius (R : ℝ) (n : ℕ) : ℝ := R / 4^(n+1)

 theorem annularRadius_pos {R : ℝ} (hR : 0 < R) (n : ℕ) : 0 < annularRadius R n := by
  exact div_pos hR (pow_pos (by norm_num) _)

 theorem annularRadius_antitone {R : ℝ} (hR : 0 ≤ R) : Antitone (annularRadius R) := by
  intro i j hij
  exact div_le_div_of_nonneg_left hR (pow_pos (by norm_num) _)
    (pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right hij 1))

 theorem annularRadius_separated {R : ℝ} (hR : 0 < R) {i j : ℕ} (hij : i < j) :
    2*annularRadius R j < annularRadius R i := by
  have hi : 0 < (4 : ℝ)^(i+1) := pow_pos (by norm_num) _
  have hj : 0 < (4 : ℝ)^(j+1) := pow_pos (by norm_num) _
  have hpow : (4 : ℝ)^(i+1)*4 ≤ 4^(j+1) := by
    rw [← pow_succ]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  change 2*(R / 4^(j+1)) < R / 4^(i+1)
  rw [← mul_div_assoc, div_lt_div_iff₀ hj hi]
  nlinarith [mul_pos hR hi, mul_le_mul_of_nonneg_left hpow hR.le]

 theorem annularRadius_outer {R : ℝ} (hR : 0 < R) (n : ℕ) :
    2*annularRadius R n < R := by
  have hb := annularRadius_antitone hR.le (Nat.zero_le n)
  have hzero : annularRadius R 0 = R/4 := by simp [annularRadius]
  rw [hzero] at hb
  linarith

 theorem annular_cutoff_derivatives_disjoint {R : ℝ} (hR : 0 < R) (z : ℂ) (i j : ℕ)
    (hij : i ≠ j) :
    fderiv ℝ (dilatedCutoff unitAnnularCutoff (annularRadius R i)) z = 0 ∨
      fderiv ℝ (dilatedCutoff unitAnnularCutoff (annularRadius R j)) z = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact (separated_dilatedCutoff_derivatives (annularRadius_pos hR j) (annularRadius_pos hR i)
      (annularRadius_separated hR h) z).symm
  · exact separated_dilatedCutoff_derivatives (annularRadius_pos hR i) (annularRadius_pos hR j)
      (annularRadius_separated hR h) z

end CircleDomainRigidity

end

end OAI
