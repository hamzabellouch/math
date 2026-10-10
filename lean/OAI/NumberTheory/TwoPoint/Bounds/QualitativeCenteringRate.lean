import OAI.NumberTheory.TwoPoint.Walks.CanonicalRoughScale
import OAI.NumberTheory.TwoPoint.Bounds.PaddingBinCount
import OAI.NumberTheory.TwoPoint.Bounds.ComplexFinalScale

namespace OAI

/-! The small loss from summing every logarithmic bin still leaves a
negative power in the canonical qualitative centering estimate. -/

namespace TwoPointCorrelations

open Filter

lemma primeSupplyCount_small_log (W L : ℝ) (hW : 1 ≤ W) (hL : 1 ≤ L) :
    (primeSupplyCount W L : ℝ) ≤ Real.log L / 200 := by
  have hb := primeSupplyCount_mul_bound W L (by linarith) hL
  have hJ : 0 ≤ (primeSupplyCount W L : ℝ) := Nat.cast_nonneg _
  have hm := mul_nonneg hJ (show 0 ≤ 6 * W - 1 by linarith)
  nlinarith

lemma exp_double_neg_nat_lt_two (J : ℕ) (hJ : 2 ≤ J) :
    Real.exp (2 * Real.exp (-(J : ℝ))) < 2 := by
  have hj : Real.exp (-(J : ℝ)) ≤ Real.exp (-2) :=
    Real.exp_le_exp.mpr (by exact_mod_cast (show -(J : ℤ) ≤ -2 by omega))
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have harg : 2 * Real.exp (-(J : ℝ)) ≤ Real.exp (-1) := by
    calc
      _ ≤ 2 * Real.exp (-2) := mul_le_mul_of_nonneg_left hj (by norm_num)
      _ ≤ Real.exp 1 * Real.exp (-2) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = Real.exp (-1) := by rw [← Real.exp_add]; norm_num
  have hend : Real.exp (Real.exp (-1)) < 2 := by
    simpa only [Nat.cast_one] using exp_neg_nat_exp_lt_two 1 (by decide)
  exact (Real.exp_le_exp.mpr harg).trans_lt hend

lemma eventually_primeSupplyCount_two (W : ℝ) (hW : 0 < W) :
    ∀ᶠ L : ℝ in atTop, 2 ≤ primeSupplyCount W L := by
  filter_upwards [eventually_ge_atTop (Real.exp (2400 * W))] with L hL
  have hLp : 0 < L := (Real.exp_pos _).trans_le hL
  have hl : 2400 * W ≤ Real.log L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hL
  have hl0 : 0 ≤ Real.log L := le_trans (by positivity : 0 ≤ 2400 * W) hl
  unfold primeSupplyCount
  apply (Nat.le_floor_iff (by positivity : 0 ≤ ((1 / 200 : ℝ) * Real.log L) / (6 * W))).mpr
  norm_num
  apply (le_div_iff₀ (by positivity : 0 < 6 * W)).mpr
  linarith

lemma canonical_centering_bin_count_rate (L : ℝ) (J : ℕ) (hL : 1 ≤ L)
    (hJ : (J : ℝ) ≤ Real.log L / 200) :
    ((paddingBinIndices L (Real.exp (-(J : ℝ)))).card : ℝ) *
      (2 : ℝ) ^ J * canonicalRoughParameter L ^ (-11 / 10 : ℝ) ≤
        101 * L ^ (-3 / 40 : ℝ) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hβ : 0 ≤ canonicalRoughParameter L ^ (-11 / 10 : ℝ) :=
    Real.rpow_nonneg (Real.rpow_nonneg hLp.le _) _
  have hη : Real.exp (-(J : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hc := paddingBinIndices_card_linear L (Real.exp (-(J : ℝ))) hL (Real.exp_pos _) hη
  have he : Real.exp (J : ℝ) ≤ L ^ (1 / 200 : ℝ) := by
    rw [Real.rpow_def_of_pos hLp]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hrate := canonical_centering_rate_bound L hL J hJ
  calc
    _ ≤ (101 * L * Real.exp (J : ℝ)) * (2 : ℝ) ^ J *
        canonicalRoughParameter L ^ (-11 / 10 : ℝ) := by
      have hc' : ((paddingBinIndices L (Real.exp (-(J : ℝ)))).card : ℝ) ≤
          101 * L * Real.exp (J : ℝ) := by
        simpa only [Real.exp_neg, div_eq_mul_inv, inv_inv] using hc
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc' (by positivity))
        hβ
    _ = 101 * Real.exp (J : ℝ) *
        ((2 : ℝ) ^ J * L * canonicalRoughParameter L ^ (-11 / 10 : ℝ)) := by ring
    _ ≤ 101 * L ^ (1 / 200 : ℝ) * L ^ (-2 / 25 : ℝ) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left he (by norm_num)) hrate
        (mul_nonneg (mul_nonneg (by positivity) hLp.le) hβ) (by positivity)
    _ = 101 * L ^ (-3 / 40 : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add hLp]
      norm_num

end TwoPointCorrelations

end OAI
