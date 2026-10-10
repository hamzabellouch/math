import OAI.Geometry.RCD.Harmonic.RadialTimeCapacity

namespace OAI

/-! # Quantitative radial density at small times

The proved signed Gaussian lower bound for the CD coefficient suffices:
the derivative of its inverse volume factor is n + kappa D²/3.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace RegularPointCoordinates

noncomputable def radialContractionFloor (n : ℕ) (κ D t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - t) * Real.exp (-κ * D ^ 2 * (1 - (1 - t) ^ 2) / (6 * n)))

noncomputable def radialContractionDensity (n : ℕ) (κ D t : ℝ) : ℝ :=
  Real.exp (κ * D ^ 2 * (1 - (1 - t) ^ 2) / 6) / (1 - t) ^ n

theorem radialContractionFloor_pos (n : ℕ) (κ D : ℝ) {t : ℝ} (ht : t < 1) :
    0 < radialContractionFloor n κ D t := by
  unfold radialContractionFloor
  exact ENNReal.ofReal_pos.mpr (mul_pos (sub_pos.mpr ht) (Real.exp_pos _))

theorem radialContractionFloor_ne_top (n : ℕ) (κ D t : ℝ) :
    radialContractionFloor n κ D t ≠ ∞ := ENNReal.ofReal_ne_top

theorem radialContractionFloor_le_tau {K κ θ D t : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hκ : 0 ≤ κ) (hK : -κ ≤ K)
    (hθ : 0 ≤ θ) (hD : θ ≤ D) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    radialContractionFloor n κ D t ≤ tau K n (1 - t) θ := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hs : 0 ≤ 1 - (1 - t) ^ 2 := by nlinarith
  have hsq : θ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hθ hD 2
  have hKθ : -κ * D ^ 2 ≤ K * θ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hK (sq_nonneg θ),
      mul_le_mul_of_nonneg_left hsq hκ]
  apply le_trans _ (tau_signed_gaussian_lower K n θ (1 - t) hn1 hθ
    (sub_nonneg.mpr ht1) (by linarith))
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr ht1)
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right hKθ hs

theorem radialContractionDensity_zero (n : ℕ) (κ D : ℝ) :
    radialContractionDensity n κ D 0 = 1 := by
  simp [radialContractionDensity]

theorem radialContractionDensity_pos (n : ℕ) (κ D : ℝ) {t : ℝ} (ht : t < 1) :
    0 < radialContractionDensity n κ D t :=
  div_pos (Real.exp_pos _) (pow_pos (sub_pos.mpr ht) _)

theorem radialContractionFloor_inv_pow {n : ℕ} (hn : 0 < n) (κ D : ℝ)
    {t : ℝ} (ht : t < 1) :
    ((radialContractionFloor n κ D t) ^ n)⁻¹ =
      ENNReal.ofReal (radialContractionDensity n κ D t) := by
  have hp : 0 < 1 - t := sub_pos.mpr ht
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : (n : ℝ) * (-κ * D ^ 2 * (1 - (1 - t) ^ 2) / (6 * n)) =
      -(κ * D ^ 2 * (1 - (1 - t) ^ 2) / 6) := by field_simp
  rw [radialContractionFloor, ← ENNReal.ofReal_pow (mul_nonneg hp.le (Real.exp_pos _).le),
    ← ENNReal.ofReal_inv_of_pos (pow_pos (mul_pos hp (Real.exp_pos _)) _),
    radialContractionDensity, mul_pow, ← Real.exp_nat_mul, he, Real.exp_neg]
  congr 1
  field_simp

theorem radialContractionDensity_hasDerivAt_zero (n : ℕ) (κ D : ℝ) :
    HasDerivAt (radialContractionDensity n κ D)
      ((n : ℝ) + κ * D ^ 2 / 3) 0 := by
  have hbase : HasDerivAt (fun t : ℝ => 1 - t) (-1) 0 :=
    (hasDerivAt_id (0 : ℝ)).const_sub 1
  have hexp : HasDerivAt (fun t : ℝ => κ * D ^ 2 * (1 - (1 - t) ^ 2) / 6)
      (κ * D ^ 2 / 3) 0 := by
    convert (((hbase.pow 2).const_sub 1).const_mul (κ * D ^ 2)).div_const 6 using 1
    norm_num
    ring
  unfold radialContractionDensity
  convert hexp.exp.div (hbase.pow n) (by simp : (1 - (0 : ℝ)) ^ n ≠ 0) using 1
  norm_num
  ring

theorem radialContractionDensity_secant_tendsto (n : ℕ) (κ D : ℝ) :
    Tendsto (fun t : ℝ => (radialContractionDensity n κ D t - 1) / t)
      (𝓝[>] 0) (𝓝 ((n : ℝ) + κ * D ^ 2 / 3)) := by
  simpa only [radialContractionDensity_zero, zero_add, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    (radialContractionDensity_hasDerivAt_zero n κ D).tendsto_slope_zero_right

end RegularPointCoordinates

end OAI
