import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzCoreSampling
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzSamplingSum
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousDyadicPartition

namespace OAI

/-! # Finite physical dyadic assembly of a cutoff profile -/

open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def cutoffProfileSchwartz (L : ℝ) (hL : 0 < L)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) : 𝓢(E, ℂ) :=
  ((hχ.comp_homeomorph
    (((Units.mk0 L⁻¹ (inv_ne_zero hL.ne')) • ContinuousLinearEquiv.refl ℝ E).toHomeomorph)).mul_right
      (f' := Q)).toSchwartzMap ((χ.smooth'.comp (contDiff_id.const_smul L⁻¹)).mul hQ)

@[simp] theorem cutoffProfileSchwartz_apply (L : ℝ) (hL : 0 < L)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (y : E) :
    cutoffProfileSchwartz L hL χ hχ Q hQ y = χ (L⁻¹ • y) * Q y := rfl

noncomputable def profileCoreSchwartz (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) : 𝓢(E, ℂ) :=
  (homogeneousCoreCutoff_hasCompactSupport.mul_right (f' := Q)).toSchwartzMap
    (homogeneousCoreCutoff.smooth'.mul hQ)

@[simp] theorem profileCoreSchwartz_apply (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (y : E) :
    profileCoreSchwartz Q hQ y = homogeneousCoreCutoff y * Q y := rfl

theorem profileCoreSchwartz_hasCompactSupport (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    HasCompactSupport (profileCoreSchwartz Q hQ : E → ℂ) :=
  homogeneousCoreCutoff_hasCompactSupport.mul_right

theorem homogeneousAnnulusCutoff_zero_core (y : E) (hy : ‖y‖ ≤ 1 / 2) :
    homogeneousAnnulusCutoff y = 0 := by
  have hh : ‖(1 / 2 : ℝ) • y‖ ≤ 1 / 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    norm_num
    linarith [norm_nonneg y]
  rw [homogeneousAnnulusCutoff_apply, homogeneousCoreCutoff_one _ hh,
    homogeneousCoreCutoff_one _ hy, sub_self]

theorem homogeneousAnnulusCutoff_partial_sum (N : ℕ) (y : E) :
    ∑ j ∈ Finset.range N, homogeneousAnnulusCutoff (((2 : ℝ) ^ j)⁻¹ • y) =
      homogeneousCoreCutoff (((2 : ℝ) ^ N)⁻¹ • y) - homogeneousCoreCutoff y := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, homogeneousAnnulusCutoff_apply]
    have he : (1 / 2 : ℝ) • (((2 : ℝ) ^ N)⁻¹ • y) = ((2 : ℝ) ^ (N + 1))⁻¹ • y := by
      rw [smul_smul, pow_succ, mul_inv_rev]
      norm_num
    rw [he]
    ring

theorem cutoffProfileAnnulus_zero_of_large_radius (a R L : ℝ)
    (hL : 0 < L) (hRL : 2 * L ≤ R)
    (χ : 𝓢(E, ℂ)) (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    schwartzPhysicalDilation a R (by linarith)
      (cutoffProfileAnnulus a R L χ homogeneousAnnulusCutoff
        homogeneousAnnulusCutoff_hasCompactSupport Q hQ) = 0 := by
  have hRp : 0 < R := by linarith
  ext y
  rw [cutoffProfileAnnulus_physical a R L hRp hL]
  by_cases hy : L ≤ ‖y‖
  · have hz : χ (L⁻¹ • y) = 0 := by
      apply hχzero
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
      exact (one_le_inv_mul₀ hL).mpr hy
    simp [hz]
  · have hn : ‖R⁻¹ • y‖ ≤ 1 / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRp)]
      apply (inv_mul_le_iff₀ hRp).mpr
      linarith [lt_of_not_ge hy]
    simp [homogeneousAnnulusCutoff_zero_core _ hn]

theorem cutoffProfileSchwartz_dyadic_assembly (a L : ℝ) (hL : 0 < L)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (N : ℕ) (hN : 2 * L ≤ (2 : ℝ) ^ N) :
    cutoffProfileSchwartz L hL χ hχ Q hQ =
      schwartzScaledCutoff L⁻¹ χ (profileCoreSchwartz Q hQ)
        (profileCoreSchwartz_hasCompactSupport Q hQ) +
      ∑ j ∈ Finset.range N, schwartzPhysicalDilation a ((2 : ℝ) ^ j) (by positivity)
        (cutoffProfileAnnulus a ((2 : ℝ) ^ j) L χ homogeneousAnnulusCutoff
          homogeneousAnnulusCutoff_hasCompactSupport Q hQ) := by
  ext y
  simp only [cutoffProfileSchwartz_apply, add_apply, schwartzScaledCutoff_apply,
    profileCoreSchwartz_apply, sum_apply]
  simp_rw [cutoffProfileAnnulus_physical a ((2 : ℝ) ^ _) L (by positivity) hL]
  rw [← Finset.sum_mul, ← Finset.sum_mul, homogeneousAnnulusCutoff_partial_sum]
  by_cases hy : L ≤ ‖y‖
  · have hz : χ (L⁻¹ • y) = 0 := by
      apply hχzero
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
      exact (one_le_inv_mul₀ hL).mpr hy
    simp [hz]
  · have hn : ‖((2 : ℝ) ^ N)⁻¹ • y‖ ≤ 1 / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity))]
      apply (inv_mul_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ N)).mpr
      linarith [lt_of_not_ge hy]
    rw [homogeneousCoreCutoff_one _ hn]
    ring

end DefocusingNLS

end OAI
