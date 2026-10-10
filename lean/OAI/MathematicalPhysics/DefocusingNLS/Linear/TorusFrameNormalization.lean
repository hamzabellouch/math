import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphFrameBounds

namespace OAI

/-! # One frame scale controls every mixed endpoint block -/

namespace DefocusingNLS

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem stableNormalized_projectedBlock (K : ℝ) (hK : K ≠ 0)
    (ζ₀ ζ₁ : F →L[ℝ] E) (π₀ π₁ : E →L[ℝ] F) (A : E →L[ℝ] E) :
    stableProjectedBlock (stableNormalizedFrame K ζ₀) (stableNormalizedFrame K ζ₁)
      (stableNormalizedCoordinate K π₀) (stableNormalizedCoordinate K π₁) A =
      stableProjectedBlock ζ₀ ζ₁ π₀ π₁ A := by
  unfold stableProjectedBlock
  rw [stableNormalized_projection K hK, stableNormalized_projection K hK]

theorem exists_uniform_frame_scale (CP CA Cζ : ℝ)
    (hCP : 0 ≤ CP) (hCA : 0 ≤ CA) (hCζ : 0 ≤ Cζ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ζ₀ ζ₁ : F →L[ℝ] E) (π₁ : E →L[ℝ] F) (A : E →L[ℝ] E),
      ‖stableFrameProjection ζ₁ π₁‖ ≤ CP → ‖A‖ ≤ CA → ‖ζ₀‖ ≤ Cζ →
      ‖stableNormalizedFrame K ζ₀‖ ≤ 1 ∧
        ‖stableMixedBlock (stableNormalizedFrame K ζ₀) (stableNormalizedFrame K ζ₁)
          (stableNormalizedCoordinate K π₁) A‖ ≤ 1 / 16 := by
  let K := 1 + Cζ + 16 * (CP * CA * Cζ)
  have hp : 0 ≤ CP * CA * Cζ := mul_nonneg (mul_nonneg hCP hCA) hCζ
  have hK : 0 < K := by dsimp [K]; positivity
  have hCK : Cζ ≤ K := by dsimp [K]; linarith
  have hlarge : 16 * (CP * CA * Cζ) ≤ K := by dsimp [K]; linarith
  refine ⟨K, hK, ?_⟩
  intro ζ₀ ζ₁ π₁ A hP hA hζ
  refine ⟨(stableNormalizedFrame_norm_le K Cζ hK ζ₀ hζ).trans ?_, ?_⟩
  · exact (div_le_one hK).mpr hCK
  · exact stableNormalized_mixed_norm_le K CP CA Cζ hK hCP hCA hCζ hlarge
      ζ₀ ζ₁ π₁ A hP hA hζ

end DefocusingNLS

end OAI
