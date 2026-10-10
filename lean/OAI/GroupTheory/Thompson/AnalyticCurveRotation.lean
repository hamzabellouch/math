import OAI.GroupTheory.Thompson.AnalyticCurveBounds
import OAI.GroupTheory.Thompson.AnalyticRotation

namespace OAI

/-!
# The explicit orthogonal operators along the actual curve
-/

noncomputable section

namespace ThompsonNonamenability.Analytic

open scoped InnerProductSpace

def R (t : ℝ) : Hilbert →L[ℝ] Hilbert := rotation (u t) (v t)

theorem R_apply_u (t : ℝ) : R t (u t) = v t :=
  rotation_apply_self _ _ (u_norm t) (v_norm t) (u_inner_v_nonneg t)

theorem R_inner (t : ℝ) (x y : Hilbert) :
    inner (𝕜 := ℝ) (R t x) (R t y) = inner (𝕜 := ℝ) x y :=
  rotation_inner _ _ (u_norm t) (v_norm t) (u_inner_v_nonneg t) x y

theorem R_norm (t : ℝ) (x : Hilbert) : ‖R t x‖ = ‖x‖ :=
  rotation_norm _ _ (u_norm t) (v_norm t) (u_inner_v_nonneg t) x

theorem R_perp (t : ℝ) (e : Hilbert) (he : inner (𝕜 := ℝ) e (u t) = 0) :
    inner (𝕜 := ℝ) (R t e) (v t) = 0 := by
  rw [← R_apply_u t, R_inner, he]

theorem R_early {t : ℝ} (ht : t ≤ 1) : R t = ContinuousLinearMap.id ℝ Hilbert := by
  rw [R, u_of_le_one ht, rotation_self]

theorem R_early_apply {t : ℝ} (ht : t ≤ 1) (e : Hilbert) : R t e = e := by
  rw [R_early ht]
  rfl

theorem lipschitzWith_R : LipschitzWith 238 R :=
  rotation_lipschitzWith_238 u v u_norm v_norm u_inner_v_nonneg
    lipschitzWith_u lipschitzWith_v

theorem R_sub_norm_le (s t : ℝ) (e : Hilbert) :
    ‖R t e - R s e‖ ≤ 238 * |t - s| * ‖e‖ := by
  have hop : ‖R t - R s‖ ≤ 238 * |t - s| := by
    simpa [dist_eq_norm, Real.norm_eq_abs] using
      lipschitzWith_R.dist_le_mul t s
  calc
    ‖R t e - R s e‖ = ‖(R t - R s) e‖ := rfl
    _ ≤ ‖R t - R s‖ * ‖e‖ := (R t - R s).le_opNorm e
    _ ≤ (238 * |t - s|) * ‖e‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg e)

end ThompsonNonamenability.Analytic

end

end OAI
