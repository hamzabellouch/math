import OAI.GroupTheory.Thompson.TubeRegularCurve
import OAI.GroupTheory.Thompson.TubeTangent

namespace OAI

/-!
# Comparing parameters of nearby normal points

Separation first puts the parameters in the range of the tangent projection
estimate. Orthogonality then bounds the remaining projection error by the
variation of the tangent. No nearest-point selection is used here.
-/

noncomputable section

universe uE

namespace ThompsonNonamenability.Analytic

open scoped InnerProductSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace RegularCurveData

variable (C : RegularCurveData E)

/-- Normal parameters of two nearby points in the tube satisfy a uniform
comparison estimate. -/
theorem parameter_comparison (x y : E) (s t : ℝ)
    (hx : ‖x - C.curve s‖ < C.rho) (hy : ‖y - C.curve t‖ < C.rho)
    (hxy : ‖x - y‖ < C.rho)
    (hperp_x : inner (𝕜 := ℝ) (x - C.curve s) (C.tangent s) = 0)
    (hperp_y : inner (𝕜 := ℝ) (y - C.curve t) (C.tangent t) = 0) :
    |t - s| ≤ 16 * ‖x - y‖ := by
  have hcurve : ‖C.curve t - C.curve s‖ < 3 * C.rho := by
    have h₁ := norm_sub_le_norm_sub_add_norm_sub (C.curve t) y x
    have h₂ := norm_sub_le_norm_sub_add_norm_sub (C.curve t) x (C.curve s)
    rw [norm_sub_rev (C.curve t) y, norm_sub_rev y x] at h₁
    linarith
  have hst : |t - s| ≤ 1 / 32 := by
    apply le_of_not_gt
    intro hlarge
    have hsep := C.separated s t (le_of_lt hlarge)
    have hrho := C.rho_pos
    have hfour := C.four_rho_lt_separation
    linarith
  have htan : ‖C.tangent s - C.tangent t‖ ≤ 16 * |t - s| := by
    simpa only [norm_sub_rev (C.tangent t) (C.tangent s)] using
      C.tangent_lipschitz s t
  have herror :
      |inner (𝕜 := ℝ) (y - C.curve t) (C.tangent s - C.tangent t)| ≤
        C.rho * 16 * |t - s| := by
    calc
      |inner (𝕜 := ℝ) (y - C.curve t) (C.tangent s - C.tangent t)|
          ≤ ‖y - C.curve t‖ * ‖C.tangent s - C.tangent t‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ ‖y - C.curve t‖ * (16 * |t - s|) :=
        mul_le_mul_of_nonneg_left htan (norm_nonneg _)
      _ ≤ C.rho * (16 * |t - s|) :=
        mul_le_mul_of_nonneg_right (le_of_lt hy) (by positivity)
      _ = C.rho * 16 * |t - s| := (mul_assoc _ _ _).symm
  have hpoint : |inner (𝕜 := ℝ) (y - x) (C.tangent s)| ≤ ‖x - y‖ := by
    calc
      |inner (𝕜 := ℝ) (y - x) (C.tangent s)| ≤ ‖y - x‖ * ‖C.tangent s‖ :=
        abs_real_inner_le_norm _ _
      _ = ‖x - y‖ := by rw [C.norm_tangent, mul_one, norm_sub_rev]
  have hidentity :
      inner (𝕜 := ℝ) (C.curve t - C.curve s) (C.tangent s) =
        inner (𝕜 := ℝ) (y - x) (C.tangent s) -
          inner (𝕜 := ℝ) (y - C.curve t) (C.tangent s - C.tangent t) := by
    simp only [inner_sub_left, inner_sub_right] at hperp_x hperp_y ⊢
    linarith
  have hupper :
      |inner (𝕜 := ℝ) (C.curve t - C.curve s) (C.tangent s)| ≤
        ‖x - y‖ + C.rho * 16 * |t - s| := by
    rw [hidentity]
    calc
      |inner (𝕜 := ℝ) (y - x) (C.tangent s) -
          inner (𝕜 := ℝ) (y - C.curve t) (C.tangent s - C.tangent t)|
          ≤ |inner (𝕜 := ℝ) (y - x) (C.tangent s)| +
            |inner (𝕜 := ℝ) (y - C.curve t) (C.tangent s - C.tangent t)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (inner (𝕜 := ℝ) (y - x) (C.tangent s)) 0
            (inner (𝕜 := ℝ) (y - C.curve t) (C.tangent s - C.tangent t))
      _ ≤ ‖x - y‖ + C.rho * 16 * |t - s| := add_le_add hpoint herror
  have hlower := C.tangent_projection_lower s t hst
  have hsmall : C.rho * 16 * |t - s| ≤ (1 / 32) * |t - s| :=
    mul_le_mul_of_nonneg_right (le_of_lt C.tangent_error_small) (abs_nonneg _)
  linarith

end RegularCurveData

end ThompsonNonamenability.Analytic

end

end OAI
