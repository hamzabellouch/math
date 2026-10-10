import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffAnnulusUniform

namespace OAI

/-! # Exact tail beyond a fixed compact core of the cutoff profile -/

open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem cutoffProfile_core_zero (R : ℝ) (hR : 0 < R)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (y : E) (hy : R ≤ ‖y‖) :
    cutoffProfileSchwartz R hR homogeneousCoreCutoff homogeneousCoreCutoff_hasCompactSupport Q hQ y = 0 := by
  rw [cutoffProfileSchwartz_apply, homogeneousCoreCutoff_zero, zero_mul]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
  exact (one_le_inv_mul₀ hR).mpr hy

theorem cutoffProfileSchwartz_tail_assembly (a L : ℝ) (hL : 0 < L)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (hχone : ∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (J M : ℕ)
    (hJM : J ≤ M) (hJ : 2 * (2 : ℝ) ^ J ≤ L) (hM : 2 * L ≤ (2 : ℝ) ^ M) :
    cutoffProfileSchwartz L hL χ hχ Q hQ -
        cutoffProfileSchwartz ((2 : ℝ) ^ J) (by positivity)
          homogeneousCoreCutoff homogeneousCoreCutoff_hasCompactSupport Q hQ =
      ∑ j ∈ Finset.Ico J M, schwartzPhysicalDilation a ((2 : ℝ) ^ j) (by positivity)
        (cutoffProfileAnnulus a ((2 : ℝ) ^ j) L χ homogeneousAnnulusCutoff
          homogeneousAnnulusCutoff_hasCompactSupport Q hQ) := by
  ext y
  simp only [sub_apply, cutoffProfileSchwartz_apply, sum_apply]
  simp_rw [cutoffProfileAnnulus_physical a ((2 : ℝ) ^ _) L (by positivity) hL]
  rw [← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_Ico_eq_sub _ hJM,
    homogeneousAnnulusCutoff_partial_sum, homogeneousAnnulusCutoff_partial_sum]
  have hstart : homogeneousCoreCutoff (((2 : ℝ) ^ J)⁻¹ • y) * χ (L⁻¹ • y) =
      homogeneousCoreCutoff (((2 : ℝ) ^ J)⁻¹ • y) := by
    by_cases hy : (2 : ℝ) ^ J ≤ ‖y‖
    · have hz : homogeneousCoreCutoff (((2 : ℝ) ^ J)⁻¹ • y) = 0 := by
        apply homogeneousCoreCutoff_zero
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
        exact (one_le_inv_mul₀ (by positivity : 0 < (2 : ℝ) ^ J)).mpr hy
      rw [hz, zero_mul]
    · have hz : χ (L⁻¹ • y) = 1 := by
        apply hχone
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
        apply (inv_mul_le_iff₀ hL).mpr
        linarith [lt_of_not_ge hy]
      rw [hz, mul_one]
  have hend : homogeneousCoreCutoff (((2 : ℝ) ^ M)⁻¹ • y) * χ (L⁻¹ • y) = χ (L⁻¹ • y) := by
    by_cases hy : L ≤ ‖y‖
    · have hz : χ (L⁻¹ • y) = 0 := by
        apply hχzero
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
        exact (one_le_inv_mul₀ hL).mpr hy
      rw [hz, mul_zero]
    · have hz : homogeneousCoreCutoff (((2 : ℝ) ^ M)⁻¹ • y) = 1 := by
        apply homogeneousCoreCutoff_one
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
        apply (inv_mul_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ M)).mpr
        linarith [lt_of_not_ge hy]
      rw [hz, one_mul]
  calc
    χ (L⁻¹ • y) * Q y - homogeneousCoreCutoff (((2 : ℝ) ^ J)⁻¹ • y) * Q y =
        (homogeneousCoreCutoff (((2 : ℝ) ^ M)⁻¹ • y) * χ (L⁻¹ • y) -
          homogeneousCoreCutoff (((2 : ℝ) ^ J)⁻¹ • y) * χ (L⁻¹ • y)) * Q y := by
      rw [hstart, hend]
      ring
    _ = _ := by ring

end DefocusingNLS

end OAI
