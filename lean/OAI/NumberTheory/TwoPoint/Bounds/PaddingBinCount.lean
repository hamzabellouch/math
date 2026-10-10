import OAI.NumberTheory.TwoPoint.Walks.RetainedRowScale
import OAI.NumberTheory.TwoPoint.Bounds.PaddingBinCoverage

namespace OAI

/-! Bounds for the actual finite bin set at eta = exp(-J). -/

namespace TwoPointCorrelations

open Filter

lemma paddingBinIndices_card_linear (L η : ℝ) (hL : 1 ≤ L)
    (hη : 0 < η) (hηone : η ≤ 1) :
    ((paddingBinIndices L η).card : ℝ) ≤ 101 * L / η := by
  have hb := paddingBinIndices_card L η (by linarith) hη
  have hratio : 1 ≤ L / η := (one_le_div hη).mpr (by linarith)
  have he : 101 * L / η = 100 * L / η + L / η := by ring
  rw [he]
  linarith

lemma paddingBinIndices_card_polynomial (L W : ℝ) (hL : 101 ≤ L) (hW : 1 ≤ W) :
    ((paddingBinIndices L (Real.exp (-(primeSupplyCount W L : ℝ)))).card : ℝ) ≤
      Real.exp (3 * Real.log L) := by
  have hLp : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hJ := primeSupplyCount_le_log W L hW hLone
  have he : Real.exp (primeSupplyCount W L) ≤ L := by
    simpa only [Real.exp_log hLp] using Real.exp_le_exp.mpr hJ
  have hη : Real.exp (-(primeSupplyCount W L : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hb := paddingBinIndices_card_linear L (Real.exp (-(primeSupplyCount W L : ℝ)))
    hLone (Real.exp_pos _) hη
  calc
    _ ≤ 101 * L / Real.exp (-(primeSupplyCount W L : ℝ)) := hb
    _ = 101 * L * Real.exp (primeSupplyCount W L) := by rw [Real.exp_neg]; field_simp
    _ ≤ 101 * L * L := mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ L ^ 3 := by
      have hx := mul_le_mul_of_nonneg_right hL (sq_nonneg L)
      nlinarith
    _ = _ := by
      rw [show 3 * Real.log L = (3 : ℕ) * Real.log L by norm_num,
        Real.exp_nat_mul, Real.exp_log hLp]

end TwoPointCorrelations

end OAI
