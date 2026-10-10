import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphReconstruction

namespace OAI

/-! # A normalized right inverse bounds its coordinate normalization from below -/

namespace DefocusingNLS
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Nontrivial V]

theorem normalized_coordinate_lower_bound (K B : ℝ) (hK : 0 ≤ K)
    (κ : E →L[ℝ] V) (hκ : ‖κ‖ ≤ B) (ζ : V →L[ℝ] E) (hζ : ‖ζ‖ ≤ 1)
    (hinv : ∀ v, (K • κ) (ζ v) = v) : 1 ≤ K * B := by
  have he : (K • κ).comp ζ = ContinuousLinearMap.id ℝ V := by
    ext v
    exact hinv v
  have h := ContinuousLinearMap.opNorm_comp_le (K • κ) ζ
  rw [he, ContinuousLinearMap.norm_id, norm_smul, Real.norm_eq_abs, abs_of_nonneg hK] at h
  calc
    1 ≤ K * ‖κ‖ * ‖ζ‖ := h
    _ ≤ K * B * 1 := mul_le_mul (mul_le_mul_of_nonneg_left hκ hK) hζ
      (norm_nonneg _) (mul_nonneg hK ((norm_nonneg κ).trans hκ))
    _ = _ := mul_one _

theorem normalized_stable_projection_bound (K B : ℝ) (hK : 0 ≤ K)
    (κ : E →L[ℝ] V) (hκ : ‖κ‖ ≤ B) (ζ : V →L[ℝ] E) (hζ : ‖ζ‖ ≤ 1)
    (hinv : ∀ v, (K • κ) (ζ v) = v) (f : E) :
    ‖stableFrameProjection ζ (K • κ) f‖ ≤ 2 * K * B * ‖f‖ := by
  have hlower := normalized_coordinate_lower_bound K B hK κ hκ ζ hζ hinv
  have hπ : ‖K • κ‖ ≤ K * B := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hK]
    exact mul_le_mul_of_nonneg_left hκ hK
  have hb : ‖ζ ((K • κ) f)‖ ≤ K * B * ‖f‖ := by
    calc
      _ ≤ ‖ζ‖ * ‖(K • κ) f‖ := ζ.le_opNorm _
      _ ≤ 1 * ((K * B) * ‖f‖) :=
        mul_le_mul hζ (((K • κ).le_opNorm f).trans
          (mul_le_mul_of_nonneg_right hπ (norm_nonneg _))) (norm_nonneg _)
          (by norm_num)
      _ = _ := one_mul _
  change ‖f - ζ ((K • κ) f)‖ ≤ _
  exact (norm_sub_le _ _).trans (by nlinarith [mul_le_mul_of_nonneg_right hlower (norm_nonneg f)])

end DefocusingNLS

end OAI
