import Mathlib

namespace OAI

noncomputable section

open scoped InnerProductSpace

namespace Problem367

section LiftGram

variable {𝕜 E F G : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

theorem lift_cross_bound_of_operator (A : E →ₗᵢ[𝕜] G) (B : F →ₗᵢ[𝕜] G)
    (T : F →L[𝕜] E) {ρ : ℝ} (hT : ‖T‖ ≤ ρ)
    (hinner : ∀ x y, inner 𝕜 (A x) (B y) = inner 𝕜 x (T y)) :
    ∀ x y, ‖inner 𝕜 (A x) (B y)‖ ≤ ρ * ‖x‖ * ‖y‖ := by
  intro x y
  rw [hinner]
  calc
    ‖inner 𝕜 x (T y)‖ ≤ ‖x‖ * ‖T y‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖T‖ * ‖y‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm y) (norm_nonneg _)
    _ ≤ ‖x‖ * (ρ * ‖y‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hT (norm_nonneg _)) (norm_nonneg _)
    _ = ρ * ‖x‖ * ‖y‖ := by ring

theorem lift_sum_gram_bounds (A : E →ₗᵢ[𝕜] G) (B : F →ₗᵢ[𝕜] G)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hcross : ∀ x y, ‖inner 𝕜 (A x) (B y)‖ ≤ ρ * ‖x‖ * ‖y‖) (x : E) (y : F) :
    (1 - ρ) * (‖x‖ ^ 2 + ‖y‖ ^ 2) ≤ ‖A x + B y‖ ^ 2 ∧
      ‖A x + B y‖ ^ 2 ≤ (1 + ρ) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have hc := (RCLike.abs_re_le_norm (inner 𝕜 (A x) (B y))).trans (hcross x y)
  have hl := (abs_le.mp hc).1
  have hu := (abs_le.mp hc).2
  have hdiff : 0 ≤ ρ * (‖x‖ - ‖y‖) ^ 2 := mul_nonneg hρ (sq_nonneg _)
  rw [norm_add_sq (𝕜 := 𝕜), A.norm_map, B.norm_map]
  constructor <;> nlinarith

theorem lift_sum_norm_lower_bound (A : E →ₗᵢ[𝕜] G) (B : F →ₗᵢ[𝕜] G)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcross : ∀ x y, ‖inner 𝕜 (A x) (B y)‖ ≤ ρ * ‖x‖ * ‖y‖) (z : E × F) :
    Real.sqrt (1 - ρ) * ‖z‖ ≤ ‖A z.1 + B z.2‖ := by
  have hpos : 0 ≤ 1 - ρ := by linarith
  have hlow := (lift_sum_gram_bounds A B hρ hcross z.1 z.2).1
  have hsqrt := Real.sq_sqrt hpos
  have hfst : Real.sqrt (1 - ρ) * ‖z.1‖ ≤ ‖A z.1 + B z.2‖ := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      (norm_nonneg _)).mp
    rw [mul_pow, hsqrt]
    nlinarith [mul_nonneg hpos (sq_nonneg ‖z.2‖)]
  have hsnd : Real.sqrt (1 - ρ) * ‖z.2‖ ≤ ‖A z.1 + B z.2‖ := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      (norm_nonneg _)).mp
    rw [mul_pow, hsqrt]
    nlinarith [mul_nonneg hpos (sq_nonneg ‖z.1‖)]
  rw [Prod.norm_def, mul_max_of_nonneg]
  · exact max_le hfst hsnd
  · exact Real.sqrt_nonneg _

theorem lift_sum_injective (A : E →ₗᵢ[𝕜] G) (B : F →ₗᵢ[𝕜] G)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcross : ∀ x y, ‖inner 𝕜 (A x) (B y)‖ ≤ ρ * ‖x‖ * ‖y‖) :
    Function.Injective (fun z : E × F => A z.1 + B z.2) := by
  let R := A.toContinuousLinearMap.coprod B.toContinuousLinearMap
  have hbound : ∃ c > 0, ∀ z, c * ‖z‖ ≤ ‖R z‖ :=
    ⟨Real.sqrt (1 - ρ), Real.sqrt_pos.2 (by linarith),
      lift_sum_norm_lower_bound A B hρ hρ1 hcross⟩
  obtain ⟨K, hK⟩ := (antilipschitzWith_iff_exists_mul_le_norm (f := R)).2 hbound
  exact hK.injective

theorem lift_sum_isClosed_range [CompleteSpace E] [CompleteSpace F]
    (A : E →ₗᵢ[𝕜] G) (B : F →ₗᵢ[𝕜] G)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcross : ∀ x y, ‖inner 𝕜 (A x) (B y)‖ ≤ ρ * ‖x‖ * ‖y‖) :
    IsClosed (Set.range (fun z : E × F => A z.1 + B z.2)) := by
  let R := A.toContinuousLinearMap.coprod B.toContinuousLinearMap
  have hbound : ∃ c > 0, ∀ z, c * ‖z‖ ≤ ‖R z‖ :=
    ⟨Real.sqrt (1 - ρ), Real.sqrt_pos.2 (by linarith),
      lift_sum_norm_lower_bound A B hρ hρ1 hcross⟩
  obtain ⟨K, hK⟩ := (antilipschitzWith_iff_exists_mul_le_norm (f := R)).2 hbound
  exact hK.isClosed_range R.uniformContinuous

def liftSumL2 (A : E →ₗᵢ[𝕜] G) (B : F →ₗᵢ[𝕜] G) :
    WithLp 2 (E × F) →L[𝕜] G :=
  (A.toContinuousLinearMap.comp (WithLp.fstL 2 𝕜 E F)) +
    (B.toContinuousLinearMap.comp (WithLp.sndL 2 𝕜 E F))

@[simp] theorem liftSumL2_apply (A : E →ₗᵢ[𝕜] G) (B : F →ₗᵢ[𝕜] G)
    (z : WithLp 2 (E × F)) : liftSumL2 A B z = A z.fst + B z.snd := rfl

theorem liftSumL2_gram_bounds (A : E →ₗᵢ[𝕜] G) (B : F →ₗᵢ[𝕜] G)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hcross : ∀ x y, ‖inner 𝕜 (A x) (B y)‖ ≤ ρ * ‖x‖ * ‖y‖)
    (z : WithLp 2 (E × F)) :
    (1 - ρ) * ‖z‖ ^ 2 ≤ ‖liftSumL2 A B z‖ ^ 2 ∧
      ‖liftSumL2 A B z‖ ^ 2 ≤ (1 + ρ) * ‖z‖ ^ 2 := by
  simpa only [WithLp.prod_norm_sq_eq_of_L2, liftSumL2_apply] using
    lift_sum_gram_bounds A B hρ hcross z.fst z.snd

theorem liftSumL2_norm_lower_bound (A : E →ₗᵢ[𝕜] G) (B : F →ₗᵢ[𝕜] G)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcross : ∀ x y, ‖inner 𝕜 (A x) (B y)‖ ≤ ρ * ‖x‖ * ‖y‖)
    (z : WithLp 2 (E × F)) :
    Real.sqrt (1 - ρ) * ‖z‖ ≤ ‖liftSumL2 A B z‖ := by
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (norm_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 - ρ)]
  exact (liftSumL2_gram_bounds A B hρ hcross z).1

theorem norm_liftSumL2_le (A : E →ₗᵢ[𝕜] G) (B : F →ₗᵢ[𝕜] G)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hcross : ∀ x y, ‖inner 𝕜 (A x) (B y)‖ ≤ ρ * ‖x‖ * ‖y‖) :
    ‖liftSumL2 A B‖ ≤ Real.sqrt (1 + ρ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro z
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 + ρ)]
  exact (liftSumL2_gram_bounds A B hρ hcross z).2

theorem liftSumL2_antilipschitz (A : E →ₗᵢ[𝕜] G) (B : F →ₗᵢ[𝕜] G)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcross : ∀ x y, ‖inner 𝕜 (A x) (B y)‖ ≤ ρ * ‖x‖ * ‖y‖) :
    AntilipschitzWith ⟨(Real.sqrt (1 - ρ))⁻¹, by positivity⟩ (liftSumL2 A B) := by
  apply ContinuousLinearMap.antilipschitz_of_bound
  intro z
  have hs : 0 < Real.sqrt (1 - ρ) := Real.sqrt_pos.2 (by linarith)
  have h := liftSumL2_norm_lower_bound A B hρ hρ1 hcross z
  change ‖z‖ ≤ (Real.sqrt (1 - ρ))⁻¹ * ‖liftSumL2 A B z‖
  exact (le_inv_mul_iff₀ hs).2 h

def liftSumL2EquivRange [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
    (A : E →ₗᵢ[𝕜] G) (B : F →ₗᵢ[𝕜] G)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcross : ∀ x y, ‖inner 𝕜 (A x) (B y)‖ ≤ ρ * ‖x‖ * ‖y‖) :
    WithLp 2 (E × F) ≃L[𝕜] (liftSumL2 A B).range :=
  (liftSumL2 A B).equivRange
    (liftSumL2_antilipschitz A B hρ hρ1 hcross).injective
    ((liftSumL2_antilipschitz A B hρ hρ1 hcross).isClosed_range
      (liftSumL2 A B).uniformContinuous)

end LiftGram

end Problem367

end

end OAI
