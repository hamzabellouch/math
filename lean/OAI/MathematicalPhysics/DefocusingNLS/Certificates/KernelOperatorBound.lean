import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphFrameBounds

namespace OAI

/-! # Turning a unit-ball kernel estimate into a stable block estimate -/

namespace DefocusingNLS

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem linear_kernel_bound_of_unit_ball (A : E →L[ℝ] G) (π : E →L[ℝ] F)
    (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ v, ‖v‖ ≤ 1 → π v = 0 → ‖A v‖ ≤ c) :
    ∀ v, π v = 0 → ‖A v‖ ≤ c * ‖v‖ := by
  let B := A.comp π.ker.subtypeL
  have hB : ‖B‖ ≤ c := ContinuousLinearMap.opNorm_le_of_unit_norm hc (fun v hv =>
    h v (le_of_eq hv) v.property)
  intro v hv
  exact (B.le_opNorm ⟨v, hv⟩).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg v))

theorem stableProjectedBlock_of_kernel_bound
    (ζ₀ ζ₁ : F →L[ℝ] E) (π₀ π₁ : E →L[ℝ] F) (A : E →L[ℝ] E)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hπζ : ∀ v, π₀ (ζ₀ v) = v)
    (hP₀ : ‖stableFrameProjection ζ₀ π₀‖ ≤ C)
    (hP₁ : ‖stableFrameProjection ζ₁ π₁‖ ≤ C)
    (hstable : ∀ v, ‖v‖ ≤ 1 → π₀ v = 0 → ‖A v‖ ≤ c) :
    ‖stableProjectedBlock ζ₀ ζ₁ π₀ π₁ A‖ ≤ C * c * C := by
  apply stableProjectedBlock_norm_le ζ₀ ζ₁ π₀ π₁ A (C * c) C
    (mul_nonneg hC hc) hC hπζ hP₀
  intro v hv
  calc
    _ ≤ C * ‖A v‖ := ((stableFrameProjection ζ₁ π₁).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hP₁ (norm_nonneg _))
    _ ≤ C * (c * ‖v‖) := mul_le_mul_of_nonneg_left
      (linear_kernel_bound_of_unit_ball A π₀ c hc hstable v hv) hC
    _ = _ := (mul_assoc _ _ _).symm

end DefocusingNLS

end OAI
