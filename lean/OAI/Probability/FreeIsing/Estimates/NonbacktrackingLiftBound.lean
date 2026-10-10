import OAI.Probability.FreeIsing.Estimates.LiftGram
import OAI.Probability.FreeIsing.Estimates.NonbacktrackingAssembly
import OAI.Probability.FreeIsing.Spectral.StablePowerTransport

namespace OAI

noncomputable section

open scoped InnerProduct

namespace Problem367.NonbacktrackingComplement

variable {𝕜 E V : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

theorem adjoint_isometric_lift_apply (F : E →ₗᵢ[𝕜] V) (x : E) :
    (F.toContinuousLinearMap†) (F x) = x := by
  have h := congrArg (fun f : E →L[𝕜] E => f x) F.adjoint_comp_self
  change (F.toContinuousLinearMap†) (F x) = x at h
  exact h

theorem isometric_lift_cross_bound
    (F H : E →ₗᵢ[𝕜] V) (A : E →L[𝕜] E) {ρ : ℝ} (hA : ‖A‖ ≤ ρ)
    (hFH : ∀ x, (F.toContinuousLinearMap†) (H x) = A x) :
    ∀ x y, ‖inner 𝕜 (F x) (H y)‖ ≤ ρ * ‖x‖ * ‖y‖ := by
  apply lift_cross_bound_of_operator F H A hA
  intro x y
  change inner 𝕜 (F.toContinuousLinearMap x) (H y) = inner 𝕜 x (A y)
  rw [← F.toContinuousLinearMap.adjoint_inner_right, hFH]

theorem norm_edgeOperator_pow_le_of_companion_bound
    (c r : ℝ) (hr : 0 ≤ r) (hcr : c - r = 1)
    (F H : E →ₗᵢ[𝕜] V) (J : V ≃ₗᵢ[𝕜] V) (A : E →L[𝕜] E)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hA : ‖A‖ ≤ ρ)
    (hFH : ∀ x, (F.toContinuousLinearMap†) (H x) = A x)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x)
    (T : (E × E) →L[𝕜] (E × E))
    (hT : ∀ x y, T (x, y) = (-(r : 𝕜) • y, x + (c : 𝕜) • A y))
    (n : ℕ) {C : ℝ} (hC : ‖T ^ n‖ ≤ C) :
    ‖edgeOperator c r F.toContinuousLinearMap H.toContinuousLinearMap J ^ n‖ ≤
      max ((‖F.toContinuousLinearMap.coprod H.toContinuousLinearMap‖ /
        Real.sqrt (1 - ρ)) * C) (r ^ n) := by
  let R := F.toContinuousLinearMap.coprod H.toContinuousLinearMap
  let N := edgeOperator c r F.toContinuousLinearMap H.toContinuousLinearMap J
  have hcross := isometric_lift_cross_bound F H A hA hFH
  have hsqrt : 0 < Real.sqrt (1 - ρ) := Real.sqrt_pos.mpr (by linarith)
  have hR : ∀ z, Real.sqrt (1 - ρ) * ‖z‖ ≤ ‖R z‖ :=
    lift_sum_norm_lower_bound F H hρ hρ1 hcross
  have hNR : ∀ z, N (R z) = R (T z) := by
    rintro ⟨x, y⟩
    change edgeOperator c r F.toContinuousLinearMap H.toContinuousLinearMap J
      (F x + H y) = R (T (x, y))
    rw [hT]
    exact edgeOperator_apply_liftSum c r hcr F.toContinuousLinearMap
      H.toContinuousLinearMap J A (adjoint_isometric_lift_apply F) hFH hJF hJH x y
  have hclosed : IsClosed ((F.toContinuousLinearMap.range ⊔
      H.toContinuousLinearMap.range : Submodule 𝕜 V) : Set V) := by
    rw [← ContinuousLinearMap.range_coprod]
    exact lift_sum_isClosed_range F H hρ hρ1 hcross
  let : CompleteSpace ↥(F.toContinuousLinearMap.range ⊔ H.toContinuousLinearMap.range) :=
    hclosed.completeSpace_coe
  apply norm_edgeOperator_pow_le_max c r hr hcr F.toContinuousLinearMap
    H.toContinuousLinearMap J A (adjoint_isometric_lift_apply F) hFH hJF hJH n
  · exact mul_nonneg (div_nonneg (norm_nonneg _) hsqrt.le) ((norm_nonneg _).trans hC)
  · intro x hx
    apply StablePowerTransport.norm_pow_apply_le_of_model_bound N T R hNR hsqrt hR n hC
    rw [ContinuousLinearMap.range_coprod]
    exact hx

end Problem367.NonbacktrackingComplement

end

end OAI
