import Mathlib

namespace OAI

noncomputable section

open scoped InnerProduct

namespace Problem367.NonbacktrackingComplement

variable {𝕜 E V : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

def liftComplement (F H : E →L[𝕜] V) : Submodule 𝕜 V :=
  (F†).ker ⊓ (H†).ker

@[simp]
theorem mem_liftComplement (F H : E →L[𝕜] V) (y : V) :
    y ∈ liftComplement F H ↔ (F†) y = 0 ∧ (H†) y = 0 := by
  rfl

theorem liftComplement_eq_orthogonal (F H : E →L[𝕜] V) :
    liftComplement F H = (F.range ⊔ H.range)ᗮ := by
  rw [liftComplement, ← F.orthogonal_range, ← H.orthogonal_range,
    Submodule.inf_orthogonal]

theorem reversal_mem_liftComplement
    (F H : E →L[𝕜] V) (J : V ≃ₗᵢ[𝕜] V)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x)
    {y : V} (hy : y ∈ liftComplement F H) :
    J y ∈ liftComplement F H := by
  rw [mem_liftComplement] at hy ⊢
  constructor
  · apply ext_inner_left 𝕜
    intro x
    rw [ContinuousLinearMap.adjoint_inner_right, inner_zero_right]
    calc
      inner 𝕜 (F x) (J y) = inner 𝕜 (J (H x)) (J y) := by rw [hJH]
      _ = inner 𝕜 (H x) y := J.inner_map_map _ _
      _ = inner 𝕜 x ((H†) y) := (H.adjoint_inner_right _ _).symm
      _ = 0 := by rw [hy.2, inner_zero_right]
  · apply ext_inner_left 𝕜
    intro x
    rw [ContinuousLinearMap.adjoint_inner_right, inner_zero_right]
    calc
      inner 𝕜 (H x) (J y) = inner 𝕜 (J (F x)) (J y) := by rw [hJF]
      _ = inner 𝕜 (F x) y := J.inner_map_map _ _
      _ = inner 𝕜 x ((F†) y) := (F.adjoint_inner_right _ _).symm
      _ = 0 := by rw [hy.1, inner_zero_right]

def edgeOperator (c r : ℝ) (F H : E →L[𝕜] V) (J : V ≃ₗᵢ[𝕜] V) :
    V →L[𝕜] V :=
  (c : 𝕜) • H.comp (F†) - (r : 𝕜) • J.toContinuousLinearEquiv.toContinuousLinearMap

theorem edgeOperator_apply_of_mem
    (c r : ℝ) (F H : E →L[𝕜] V) (J : V ≃ₗᵢ[𝕜] V)
    {y : V} (hy : y ∈ liftComplement F H) :
    edgeOperator c r F H J y = (-(r : 𝕜)) • J y := by
  have hFy := ((mem_liftComplement F H y).mp hy).1
  simp [edgeOperator, hFy]

theorem edgeOperator_mem_liftComplement
    (c r : ℝ) (F H : E →L[𝕜] V) (J : V ≃ₗᵢ[𝕜] V)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x)
    {y : V} (hy : y ∈ liftComplement F H) :
    edgeOperator c r F H J y ∈ liftComplement F H := by
  rw [edgeOperator_apply_of_mem c r F H J hy]
  exact (liftComplement F H).smul_mem (-(r : 𝕜))
    (reversal_mem_liftComplement F H J hJF hJH hy)

theorem edgeOperator_pow_mem_liftComplement
    (c r : ℝ) (F H : E →L[𝕜] V) (J : V ≃ₗᵢ[𝕜] V)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x)
    {y : V} (hy : y ∈ liftComplement F H) (n : ℕ) :
    (edgeOperator c r F H J ^ n) y ∈ liftComplement F H := by
  induction n with
  | zero => simpa using hy
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp]
      exact edgeOperator_mem_liftComplement c r F H J hJF hJH ih

theorem norm_edgeOperator_pow
    (c r : ℝ) (hr : 0 ≤ r) (F H : E →L[𝕜] V) (J : V ≃ₗᵢ[𝕜] V)
    (hJF : ∀ x, J (F x) = H x) (hJH : ∀ x, J (H x) = F x)
    {y : V} (hy : y ∈ liftComplement F H) (n : ℕ) :
    ‖(edgeOperator c r F H J ^ n) y‖ = r ^ n * ‖y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp,
        edgeOperator_apply_of_mem c r F H J
          (edgeOperator_pow_mem_liftComplement c r F H J hJF hJH hy n)]
      rw [norm_smul, norm_neg, RCLike.norm_ofReal, abs_of_nonneg hr,
        J.norm_map, ih, pow_succ]
      ring

end Problem367.NonbacktrackingComplement

end

end OAI
