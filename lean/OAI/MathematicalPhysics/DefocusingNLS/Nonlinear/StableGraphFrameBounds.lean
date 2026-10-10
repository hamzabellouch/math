import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphReconstruction

namespace OAI

/-! # Bounded frame normalization for the concrete torus blocks

The stable estimate in the manuscript is only on the coordinate kernel.
Precomposing with the bounded stable projection gives the whole-space
block used by the sequence contraction.  Scaling the finite-dimensional
frame makes the mixed block small without changing that projection.
-/

namespace DefocusingNLS

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def stableNormalizedFrame (K : ℝ) (ζ : F →L[ℝ] E) : F →L[ℝ] E :=
  K⁻¹ • ζ

noncomputable def stableNormalizedCoordinate (K : ℝ) (π : E →L[ℝ] F) : E →L[ℝ] F :=
  K • π

theorem stableNormalized_rightInverse (K : ℝ) (hK : K ≠ 0)
    (ζ : F →L[ℝ] E) (π : E →L[ℝ] F) (hπζ : ∀ v, π (ζ v) = v) (v : F) :
    stableNormalizedCoordinate K π (stableNormalizedFrame K ζ v) = v := by
  simp only [stableNormalizedCoordinate, stableNormalizedFrame, smul_apply,
    map_smul, hπζ, smul_smul, inv_mul_cancel₀ hK, one_smul]

theorem stableNormalized_projection (K : ℝ) (hK : K ≠ 0)
    (ζ : F →L[ℝ] E) (π : E →L[ℝ] F) :
    stableFrameProjection (stableNormalizedFrame K ζ) (stableNormalizedCoordinate K π) =
      stableFrameProjection ζ π := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [stableFrameProjection, sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, stableNormalizedFrame, stableNormalizedCoordinate,
    smul_apply, map_smul, smul_smul, mul_inv_cancel₀ hK, one_smul]

theorem stableNormalizedFrame_norm_le (K C : ℝ) (hK : 0 < K)
    (ζ : F →L[ℝ] E) (hζ : ‖ζ‖ ≤ C) : ‖stableNormalizedFrame K ζ‖ ≤ C / K := by
  rw [stableNormalizedFrame, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hK), div_eq_mul_inv]
  exact (mul_le_mul_of_nonneg_left hζ (inv_pos.mpr hK).le).trans_eq (mul_comm _ _)

theorem stableNormalizedCoordinate_norm_le (K C : ℝ) (hK : 0 ≤ K)
    (π : E →L[ℝ] F) (hπ : ‖π‖ ≤ C) : ‖stableNormalizedCoordinate K π‖ ≤ K * C := by
  rw [stableNormalizedCoordinate, norm_smul, Real.norm_eq_abs, abs_of_nonneg hK]
  exact mul_le_mul_of_nonneg_left hπ hK

theorem stableNormalized_defect (K : ℝ) (π₀ π₁ : E →L[ℝ] F)
    (A : E →L[ℝ] E) (D : F →L[ℝ] F) :
    (stableNormalizedCoordinate K π₁).comp A - D.comp (stableNormalizedCoordinate K π₀) =
      K • (π₁.comp A - D.comp π₀) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [stableNormalizedCoordinate, sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, map_smul, smul_sub]

theorem stableNormalized_defect_norm_le (K τ : ℝ) (hK : 0 ≤ K)
    (π₀ π₁ : E →L[ℝ] F) (A : E →L[ℝ] E) (D : F →L[ℝ] F)
    (he : ‖π₁.comp A - D.comp π₀‖ ≤ τ) :
    ‖(stableNormalizedCoordinate K π₁).comp A -
      D.comp (stableNormalizedCoordinate K π₀)‖ ≤ K * τ := by
  rw [stableNormalized_defect, norm_smul, Real.norm_eq_abs, abs_of_nonneg hK]
  exact mul_le_mul_of_nonneg_left he hK

noncomputable def stableProjectedBlock (ζ₀ ζ₁ : F →L[ℝ] E)
    (π₀ π₁ : E →L[ℝ] F) (A : E →L[ℝ] E) : E →L[ℝ] E :=
  (stableFrameProjection ζ₁ π₁).comp (A.comp (stableFrameProjection ζ₀ π₀))

noncomputable def stableMixedBlock (ζ₀ ζ₁ : F →L[ℝ] E)
    (π₁ : E →L[ℝ] F) (A : E →L[ℝ] E) : F →L[ℝ] E :=
  (stableFrameProjection ζ₁ π₁).comp (A.comp ζ₀)

theorem stableFrameProjection_eq_self (ζ : F →L[ℝ] E) (π : E →L[ℝ] F)
    (v : E) (hv : π v = 0) : stableFrameProjection ζ π v = v := by
  change v - ζ (π v) = v
  rw [hv, map_zero, sub_zero]

theorem stableProjectedBlock_norm_le (ζ₀ ζ₁ : F →L[ℝ] E)
    (π₀ π₁ : E →L[ℝ] F) (A : E →L[ℝ] E)
    (c C : ℝ) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hπζ : ∀ v, π₀ (ζ₀ v) = v) (hP : ‖stableFrameProjection ζ₀ π₀‖ ≤ C)
    (hstable : ∀ v, π₀ v = 0 → ‖stableFrameProjection ζ₁ π₁ (A v)‖ ≤ c * ‖v‖) :
    ‖stableProjectedBlock ζ₀ ζ₁ π₀ π₁ A‖ ≤ c * C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hc hC)
  intro v
  calc
    _ ≤ c * ‖stableFrameProjection ζ₀ π₀ v‖ :=
      hstable _ (stableFrameProjection_coordinate ζ₀ π₀ hπζ v)
    _ ≤ c * (C * ‖v‖) := mul_le_mul_of_nonneg_left
      (((stableFrameProjection ζ₀ π₀).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hP (norm_nonneg v))) hc
    _ = (c * C) * ‖v‖ := by ring

theorem stableProjectedBlock_norm_le_eighth (ζ₀ ζ₁ : F →L[ℝ] E)
    (π₀ π₁ : E →L[ℝ] F) (A : E →L[ℝ] E)
    (C : ℝ) (hC : 0 < C) (hπζ : ∀ v, π₀ (ζ₀ v) = v)
    (hP : ‖stableFrameProjection ζ₀ π₀‖ ≤ C)
    (hstable : ∀ v, π₀ v = 0 →
      ‖stableFrameProjection ζ₁ π₁ (A v)‖ ≤ (1 / (8 * C)) * ‖v‖) :
    ‖stableProjectedBlock ζ₀ ζ₁ π₀ π₁ A‖ ≤ 1 / 8 := by
  apply (stableProjectedBlock_norm_le ζ₀ ζ₁ π₀ π₁ A (1 / (8 * C)) C
    (by positivity) hC.le hπζ hP hstable).trans_eq
  field_simp [hC.ne']

theorem stableMixedBlock_norm_le (ζ₀ ζ₁ : F →L[ℝ] E)
    (π₁ : E →L[ℝ] F) (A : E →L[ℝ] E)
    (Cₚ Cₐ Cζ : ℝ) (hCₚ : 0 ≤ Cₚ) (hCₐ : 0 ≤ Cₐ) (hCζ : 0 ≤ Cζ)
    (hP : ‖stableFrameProjection ζ₁ π₁‖ ≤ Cₚ) (hA : ‖A‖ ≤ Cₐ) (hζ : ‖ζ₀‖ ≤ Cζ) :
    ‖stableMixedBlock ζ₀ ζ₁ π₁ A‖ ≤ Cₚ * Cₐ * Cζ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg hCₚ hCₐ) hCζ)
  intro v
  calc
    _ ≤ ‖stableFrameProjection ζ₁ π₁‖ * ‖A (ζ₀ v)‖ :=
      (stableFrameProjection ζ₁ π₁).le_opNorm _
    _ ≤ Cₚ * (Cₐ * (Cζ * ‖v‖)) := by
      apply mul_le_mul hP _ (norm_nonneg _) hCₚ
      exact (A.le_opNorm _).trans (mul_le_mul hA
        ((ζ₀.le_opNorm v).trans (mul_le_mul_of_nonneg_right hζ (norm_nonneg v)))
          (norm_nonneg _) hCₐ)
    _ = (Cₚ * Cₐ * Cζ) * ‖v‖ := by ring

theorem stableNormalized_mixed_norm_le (K Cₚ Cₐ Cζ : ℝ)
    (hK : 0 < K) (hCₚ : 0 ≤ Cₚ) (hCₐ : 0 ≤ Cₐ) (hCζ : 0 ≤ Cζ)
    (hlarge : 16 * (Cₚ * Cₐ * Cζ) ≤ K)
    (ζ₀ ζ₁ : F →L[ℝ] E) (π₁ : E →L[ℝ] F) (A : E →L[ℝ] E)
    (hP : ‖stableFrameProjection ζ₁ π₁‖ ≤ Cₚ) (hA : ‖A‖ ≤ Cₐ) (hζ : ‖ζ₀‖ ≤ Cζ) :
    ‖stableMixedBlock (stableNormalizedFrame K ζ₀) (stableNormalizedFrame K ζ₁)
      (stableNormalizedCoordinate K π₁) A‖ ≤ 1 / 16 := by
  have hP' : ‖stableFrameProjection (stableNormalizedFrame K ζ₁)
      (stableNormalizedCoordinate K π₁)‖ ≤ Cₚ := by
    rw [stableNormalized_projection K hK.ne']
    exact hP
  apply (stableMixedBlock_norm_le _ _ _ _ Cₚ Cₐ (Cζ / K) hCₚ hCₐ
    (div_nonneg hCζ hK.le) hP' hA (stableNormalizedFrame_norm_le K Cζ hK ζ₀ hζ)).trans
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hK).mpr
  nlinarith

end DefocusingNLS

end OAI
