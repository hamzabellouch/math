import OAI.NumberTheory.Ostmann.ZeroDensity.ThetaMainTerm
import OAI.NumberTheory.Ostmann.ZeroDensity.RieszSmoothRecovery

namespace OAI

/-! # The integrated principal and exceptional main term for positive unsmoothing -/

namespace Ostmann

noncomputable def integratedThetaMain (φ χ β x : ℝ) : ℝ :=
  (x ^ 2 / 2 - χ * x ^ (β + 1) / (β * (β + 1))) / φ

theorem hasDerivAt_integratedThetaMain (φ χ β : ℝ) (hβ : 0 < β)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (integratedThetaMain φ χ β) (thetaMainTerm φ χ β x) x := by
  have h := (((hasDerivAt_id x).pow 2).div_const 2).sub
    (((Real.hasDerivAt_rpow_const (p := β + 1) (.inl hx.ne')).const_mul χ).div_const (β * (β + 1)))
  have h := h.div_const φ
  norm_num only [Nat.reduceSub, pow_one, mul_one, id_eq] at h
  change HasDerivAt (integratedThetaMain φ χ β)
    ((2 * x / 2 - χ * ((β + 1) * x ^ (β + 1 - 1)) / (β * (β + 1))) / φ) x at h
  have he : (2 * x / 2 - χ * ((β + 1) * x ^ (β + 1 - 1)) / (β * (β + 1))) / φ =
      thetaMainTerm φ χ β x := by
    rw [show β + 1 - 1 = β by ring]
    unfold thetaMainTerm
    congr 1
    field_simp
  exact he ▸ h

theorem thetaMainDensity_abs_le_two (φ χ β x : ℝ)
    (hφ : 1 ≤ φ) (hχ : |χ| ≤ 1) (hβ : β ≤ 1) (hx : 1 ≤ x) :
    |thetaMainDensity φ χ β x| ≤ 2 := by
  have hφp : 0 < φ := by linarith
  have hp : 0 ≤ x ^ (β - 1) := Real.rpow_nonneg (by linarith) _
  have hpow : x ^ (β - 1) ≤ 1 := by
    have hh := Real.rpow_le_rpow_of_exponent_le hx (show β - 1 ≤ 0 by linarith)
    simpa using hh
  have hmul : |χ * x ^ (β - 1)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hp]
    exact (mul_le_mul hχ hpow hp zero_le_one).trans_eq (one_mul 1)
  have hnum : |1 - χ * x ^ (β - 1)| ≤ 2 := by
    have hh := abs_sub (1 : ℝ) (χ * x ^ (β - 1))
    norm_num only [abs_one] at hh
    linarith
  rw [thetaMainDensity, abs_div, abs_of_pos hφp]
  apply (div_le_iff₀ hφp).mpr
  linarith

theorem integratedThetaMain_remainder_pair (φ χ β x h : ℝ)
    (hφ : 1 ≤ φ) (hχ : |χ| ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hh : 0 < h) (hx : 1 ≤ x - h) :
    |integratedThetaMain φ χ β (x + h) - integratedThetaMain φ χ β x -
        h * thetaMainTerm φ χ β x| ≤ 2 * h ^ 2 ∧
      |integratedThetaMain φ χ β x - integratedThetaMain φ χ β (x - h) -
        h * thetaMainTerm φ χ β x| ≤ 2 * h ^ 2 := by
  apply smooth_main_remainder_pair (integratedThetaMain φ χ β) (thetaMainTerm φ χ β)
    (thetaMainDensity φ χ β) x h hh
  · intro t ht
    exact hasDerivAt_integratedThetaMain φ χ β hβ (by have := ht.1; linarith)
  · intro t ht
    exact hasDerivAt_thetaMainTerm φ χ β hβ.ne' (by have := ht.1; linarith)
  · intro t ht
    exact thetaMainDensity_abs_le_two φ χ β t hφ hχ hβ1 (hx.trans ht.1)

end Ostmann

end OAI
