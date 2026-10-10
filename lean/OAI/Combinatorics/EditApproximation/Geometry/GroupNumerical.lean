import OAI.Combinatorics.EditApproximation.Geometry.Parameters
import OAI.Combinatorics.EditApproximation.Geometry.GroupSampling

namespace OAI

/-! Explicit numerical slack for the shared group estimator and online increments. -/

namespace EditApproximation

theorem group_normalized_exponent {ell : ℝ} (hell : 1 ≤ ell) :
    ell ^ 37 / 3000 ≤
      ell ^ 80 * (1 / (2 * ell ^ 21)) ^ 2 /
        (512 * ell + (4 / 3 : ℝ) * (1 / (2 * ell ^ 21))) := by
  have he : 0 < ell := by linarith only [hell]
  have halpha : 0 < 1 / (2 * ell ^ 21) := by positivity
  have halpha_le : 1 / (2 * ell ^ 21) ≤ ell := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * ell ^ 21)).2
    have hpow := one_le_pow₀ hell (n := 21)
    nlinarith only [hell, hpow]
  have hden : 512 * ell + (4 / 3 : ℝ) * (1 / (2 * ell ^ 21)) ≤ 750 * ell := by
    linarith only [halpha_le, hell]
  have hnum : ell ^ 80 * (1 / (2 * ell ^ 21)) ^ 2 = ell ^ 38 / 4 := by
    field_simp
    ring
  rw [hnum]
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3000)
    (by positivity : 0 < 512 * ell + (4 / 3 : ℝ) * (1 / (2 * ell ^ 21)))).2
  have h := mul_le_mul_of_nonneg_left hden (pow_nonneg he.le 37)
  have hid : ell ^ 37 * (750 * ell) = ell ^ 38 / 4 * 3000 := by ring
  exact h.trans_eq hid

theorem group_exponent_polynomial_slack {ell : ℝ} (hell : 8 ≤ ell) :
    2 * ell ^ 2 + 20 * ell ≤ ell ^ 37 / 3000 := by
  have he : 1 ≤ ell := by linarith only [hell]
  have hcoef : (131072 : ℝ) ≤ ell ^ 33 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) hell 6
    norm_num at h
    exact (by norm_num : (131072 : ℝ) ≤ 262144) |>.trans
      (h.trans (pow_le_pow_right₀ he (by decide : 6 ≤ 33)))
  have hbig : 131072 * ell ^ 4 ≤ ell ^ 37 := by
    calc
      _ ≤ ell ^ 33 * ell ^ 4 := mul_le_mul_of_nonneg_right hcoef (pow_nonneg (by linarith only [hell]) 4)
      _ = _ := by ring
  have he2 : ell ≤ ell ^ 2 := by nlinarith only [he]
  have he4 : ell ^ 2 ≤ ell ^ 4 := pow_le_pow_right₀ he (by decide : 2 ≤ 4)
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 3000)).2
  nlinarith only [hbig, he2, he4]

/-- The union bound is below H^-4 once its literal count bounds and the
computed height/representative growth bounds have been substituted. -/
theorem group_union_failure_numeric {ell H members scales : ℝ}
    (hell : 8 ≤ ell) (hH : 0 < H) (hHexp : H ≤ Real.exp ell)
    (_hmembers : 0 ≤ members) (hmembersBound : members ≤ 4 * Real.exp (2 * ell ^ 2))
    (hscales : 0 ≤ scales) (hscalesBound : scales ≤ 2 * ell) :
    members * scales * (2 * Real.exp (-(ell ^ 37 / 3000))) ≤ 1 / H ^ 4 := by
  have he : 0 ≤ ell := by linarith only [hell]
  have hcounts : members * scales * (2 * Real.exp (-(ell ^ 37 / 3000))) ≤
      16 * ell * Real.exp (2 * ell ^ 2 - ell ^ 37 / 3000) := by
    have h := mul_le_mul hmembersBound hscalesBound hscales (by positivity : 0 ≤ 4 * Real.exp (2 * ell ^ 2))
    have h' := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ 2 * Real.exp (-(ell ^ 37 / 3000)))
    rw [sub_eq_add_neg, Real.exp_add]
    convert h' using 1
    ring
  have hpower : H ^ 4 ≤ Real.exp (4 * ell) := by
    have h := pow_le_pow_left₀ hH.le hHexp 4
    rw [← Real.exp_nat_mul] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  apply (le_div_iff₀ (pow_pos hH 4)).2
  have hnonneg : 0 ≤ 16 * ell * Real.exp (2 * ell ^ 2 - ell ^ 37 / 3000) := by positivity
  have hprod := mul_le_mul hcounts hpower (pow_nonneg hH.le 4) hnonneg
  have hexponent := group_exponent_polynomial_slack hell
  have hsmall : 2 * ell ^ 2 - ell ^ 37 / 3000 + 4 * ell ≤ -(16 * ell) := by
    linarith only [hexponent]
  have hexp := Real.exp_le_exp.mpr hsmall
  have hlinear : 16 * ell ≤ Real.exp (16 * ell) := (Real.add_one_le_exp _).trans' (by linarith)
  have hfinal : 16 * ell * Real.exp (2 * ell ^ 2 - ell ^ 37 / 3000) * Real.exp (4 * ell) ≤ 1 := by
    rw [mul_assoc, ← Real.exp_add]
    calc
      _ ≤ Real.exp (16 * ell) * Real.exp (-(16 * ell)) :=
        mul_le_mul hlinear hexp (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add]; simp only [add_neg_cancel, Real.exp_zero]
  exact hprod.trans hfinal

end EditApproximation

end OAI
