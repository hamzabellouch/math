import Mathlib

namespace OAI

noncomputable section
open scoped InnerProductSpace
namespace Problem367.ColoredEdgeLifts
variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {d : ℕ}

abbrev EdgeSpace (d : ℕ) (E : Type*) := PiLp 2 (fun _ : Fin d => E)

def tailLift (hd : 0 < d) : E →ₗᵢ[𝕜] EdgeSpace d E where
  toFun x := WithLp.toLp 2 (fun _ => (((Real.sqrt (d : ℝ))⁻¹ : ℝ) : 𝕜) • x)
  map_add' x y := by
    ext i
    simp [smul_add]
  map_smul' a x := by
    ext i
    simp [smul_smul, mul_comm]
  norm_map' x := by
    have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
    have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdreal
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2]
    change (∑ _i : Fin d, ‖((((Real.sqrt (d : ℝ))⁻¹ : ℝ) : 𝕜) • x)‖ ^ 2) = ‖x‖ ^ 2
    simp only [norm_smul, RCLike.norm_ofReal,
      abs_of_pos (inv_pos.2 hs), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_pow, inv_pow]
    rw [Real.sq_sqrt hdreal.le]
    field_simp

@[simp] theorem tailLift_apply (hd : 0 < d) (x : E) (i : Fin d) :
    tailLift (𝕜 := 𝕜) hd x i = (((Real.sqrt (d : ℝ))⁻¹ : ℝ) : 𝕜) • x := rfl

def reversal (S : Fin d → E ≃ₗᵢ[𝕜] E) : EdgeSpace d E ≃ₗᵢ[𝕜] EdgeSpace d E :=
  LinearIsometryEquiv.piLpCongrRight 2 S

@[simp] theorem reversal_apply (S : Fin d → E ≃ₗᵢ[𝕜] E) (x : EdgeSpace d E) (i : Fin d) :
    reversal S x i = S i (x i) := rfl

def headLift (hd : 0 < d) (S : Fin d → E ≃ₗᵢ[𝕜] E) : E →ₗᵢ[𝕜] EdgeSpace d E :=
  (reversal S).toLinearIsometry.comp (tailLift (𝕜 := 𝕜) hd)

@[simp] theorem headLift_apply (hd : 0 < d) (S : Fin d → E ≃ₗᵢ[𝕜] E) (x : E) (i : Fin d) :
    headLift hd S x i = (((Real.sqrt (d : ℝ))⁻¹ : ℝ) : 𝕜) • S i x := by
  change S i ((((Real.sqrt (d : ℝ))⁻¹ : ℝ) : 𝕜) • x) = _
  exact (S i).map_smul _ _

@[simp] theorem reversal_tail (hd : 0 < d) (S : Fin d → E ≃ₗᵢ[𝕜] E) (x : E) :
    reversal S (tailLift (𝕜 := 𝕜) hd x) = headLift hd S x := rfl

theorem reversal_involutive (S : Fin d → E ≃ₗᵢ[𝕜] E)
    (hS : ∀ i, Function.Involutive (S i)) : Function.Involutive (reversal S) := by
  intro x
  ext i
  exact hS i (x i)

theorem reversal_head (hd : 0 < d) (S : Fin d → E ≃ₗᵢ[𝕜] E)
    (hS : ∀ i, Function.Involutive (S i)) (x : E) :
    reversal S (headLift hd S x) = tailLift (𝕜 := 𝕜) hd x :=
  reversal_involutive S hS (tailLift (𝕜 := 𝕜) hd x)

section Adjoint
variable [CompleteSpace E]

theorem tailLift_adjoint_apply (hd : 0 < d) (y : EdgeSpace d E) :
    (tailLift (𝕜 := 𝕜) hd).toContinuousLinearMap.adjoint y =
      (((Real.sqrt (d : ℝ))⁻¹ : ℝ) : 𝕜) • ∑ i, y i := by
  apply ext_inner_left 𝕜
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply]
  simp only [LinearIsometry.coe_toContinuousLinearMap, tailLift_apply, inner_smul_left, inner_smul_right, inner_sum,
    RCLike.conj_ofReal, Finset.mul_sum]

theorem tailLift_adjoint_tail (hd : 0 < d) (x : E) :
    (tailLift (𝕜 := 𝕜) hd).toContinuousLinearMap.adjoint
      (tailLift (𝕜 := 𝕜) hd x) = x := by
  apply ext_inner_left 𝕜
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (tailLift (𝕜 := 𝕜) hd).inner_map_map y x

theorem tailLift_adjoint_head (hd : 0 < d) (S : Fin d → E ≃ₗᵢ[𝕜] E) (x : E) :
    (tailLift (𝕜 := 𝕜) hd).toContinuousLinearMap.adjoint (headLift hd S x) =
      (((d : ℝ)⁻¹ : ℝ) : 𝕜) • ∑ i, S i x := by
  rw [tailLift_adjoint_apply]
  simp only [headLift_apply, ← Finset.smul_sum, smul_smul]
  congr 1
  have hdreal : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  norm_cast
  rw [← pow_two, inv_pow, Real.sq_sqrt hdreal]

def neighborAverage (S : Fin d → E ≃ₗᵢ[𝕜] E) : E →L[𝕜] E :=
  (((d : ℝ)⁻¹ : ℝ) : 𝕜) • ∑ i, (S i).toContinuousLinearEquiv.toContinuousLinearMap

omit [CompleteSpace E] in
@[simp] theorem neighborAverage_apply (S : Fin d → E ≃ₗᵢ[𝕜] E) (x : E) :
    neighborAverage S x = (((d : ℝ)⁻¹ : ℝ) : 𝕜) • ∑ i, S i x := by
  simp [neighborAverage]

theorem tailLift_adjoint_head_eq_average (hd : 0 < d) (S : Fin d → E ≃ₗᵢ[𝕜] E) (x : E) :
    (tailLift (𝕜 := 𝕜) hd).toContinuousLinearMap.adjoint (headLift hd S x) =
      neighborAverage S x := by
  rw [tailLift_adjoint_head, neighborAverage_apply]

def forwardOperator (hd : 0 < d) (S : Fin d → E ≃ₗᵢ[𝕜] E) (r : ℝ) :
    EdgeSpace d E →L[𝕜] EdgeSpace d E :=
  (((d : ℝ) * r : ℝ) : 𝕜) •
    (headLift hd S).toContinuousLinearMap.comp (tailLift (𝕜 := 𝕜) hd).toContinuousLinearMap.adjoint -
      (r : 𝕜) • (reversal S).toContinuousLinearEquiv.toContinuousLinearMap

theorem forwardOperator_apply (hd : 0 < d) (S : Fin d → E ≃ₗᵢ[𝕜] E)
    (r : ℝ) (y : EdgeSpace d E) (i : Fin d) :
    forwardOperator hd S r y i = (r : 𝕜) • ∑ j ∈ Finset.univ.erase i, S i (y j) := by
  change (((d : ℝ) * r : ℝ) : 𝕜) •
    (headLift hd S ((tailLift (𝕜 := 𝕜) hd).toContinuousLinearMap.adjoint y) i) -
      (r : 𝕜) • reversal S y i = _
  rw [headLift_apply, tailLift_adjoint_apply, map_smul, reversal_apply]
  simp only [smul_smul]
  have hscalar : (((d : ℝ) * r : ℝ) : 𝕜) *
      ((((Real.sqrt (d : ℝ))⁻¹ : ℝ) : 𝕜) * (((Real.sqrt (d : ℝ))⁻¹ : ℝ) : 𝕜)) = (r : 𝕜) := by
    have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
    norm_cast
    rw [← pow_two, inv_pow, Real.sq_sqrt hdreal.le]
    field_simp
  rw [hscalar, ← smul_sub, map_sum]
  congr 1
  exact (Finset.sum_erase_eq_sub (f := fun j => S i (y j)) (Finset.mem_univ i)).symm

theorem isSelfAdjoint_of_involutive (S : E ≃ₗᵢ[𝕜] E)
    (hS : Function.Involutive S) :
    IsSelfAdjoint S.toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner 𝕜 (S x) y = inner 𝕜 x (S y)
  have h := S.inner_map_map x (S y)
  simpa only [hS y] using h

theorem reversal_selfAdjoint (S : Fin d → E ≃ₗᵢ[𝕜] E)
    (hS : ∀ i, Function.Involutive (S i)) :
    IsSelfAdjoint (reversal S).toContinuousLinearEquiv.toContinuousLinearMap :=
  isSelfAdjoint_of_involutive (reversal S) (reversal_involutive S hS)

theorem neighborAverage_selfAdjoint (S : Fin d → E ≃ₗᵢ[𝕜] E)
    (hS : ∀ i, Function.Involutive (S i)) : IsSelfAdjoint (neighborAverage S) := by
  unfold neighborAverage
  have hscalar : IsSelfAdjoint ((((d : ℝ)⁻¹ : ℝ) : 𝕜)) := by simp [IsSelfAdjoint]
  exact hscalar.smul (isSelfAdjoint_sum _ fun i _ => isSelfAdjoint_of_involutive (S i) (hS i))

end Adjoint

end Problem367.ColoredEdgeLifts

end

end OAI
