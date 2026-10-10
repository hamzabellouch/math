import OAI.Analysis.KadisonKastler.TracialProducts

namespace OAI

/-! # Trace-to-strong transfer from norm-density of tracial functionals

This proves the analytic transfer argument from the concrete functional
approximation property. Existence of this approximation for a normal
representation is not asserted here.
-/

namespace KadisonKastler

noncomputable section

variable {B H : Type*} [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Norm approximation of every vector functional by a trace functional.
The order of the inner product makes the vector functional complex-linear. -/
def TraceVectorApproximation (τ : FaithfulTracialState B)
    (ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H)) : Prop :=
  ∀ z : H, ∀ ε : ℝ, 0 < ε → ∃ b : B, ∀ a : B,
    ‖inner ℂ z (ρ a z) - τ.toLinearMap (b * a)‖ ≤ ε * ‖a‖

/-- Cauchy–Schwarz bounds the trace functional on a positive square by
its two-norm and the ambient bound. -/
theorem trace_positive_square_functional_le (τ : FaithfulTracialState B) (b x : B) :
    ‖τ.toLinearMap (b * (star x * x))‖ ≤ ‖b‖ * ‖x‖ * traceTwoNorm τ x := by
  have hcs := τ.cauchySchwarz (star b) (star x * x)
  simp only [star_star, traceTwoNorm_star] at hcs
  have hmul : traceTwoNorm τ (star x * x) ≤ ‖x‖ * traceTwoNorm τ x := by
    simpa only [norm_star] using traceTwoNorm_mul_le_left τ (star x) x
  calc
    _ ≤ traceTwoNorm τ b * traceTwoNorm τ (star x * x) := hcs
    _ ≤ ‖b‖ * (‖x‖ * traceTwoNorm τ x) :=
      mul_le_mul (traceTwoNorm_le_norm τ b) hmul (traceTwoNorm_nonneg τ _) (norm_nonneg b)
    _ = _ := by ring

/-- Norm-density of the trace functionals implies strong continuity of
the tracial two-norm on every bounded ball. -/
theorem TraceVectorApproximation.strongContinuous
    {τ : FaithfulTracialState B} {ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H)}
    (h : TraceVectorApproximation τ ρ) : TraceStrongContinuous τ ρ := by
  intro z C hC ε hε
  let α : ℝ := ε ^ 2 / (4 * (C ^ 2 + 1))
  have hα : 0 < α := by dsimp [α]; positivity
  obtain ⟨b, hb⟩ := h z α hα
  let η : ℝ := ε ^ 2 / (4 * (‖b‖ * (C + 1) + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨η, hη, ?_⟩
  intro x hx hx2
  have he : inner ℂ z (ρ (star x * x) z) = (‖ρ x z‖ ^ 2 : ℝ) := by
    simp only [map_mul, map_star, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    rfl
  have hsq : ‖star x * x‖ ≤ C ^ 2 := by
    rw [CStarRing.norm_star_mul_self, ← pow_two]
    exact pow_le_pow_left₀ (norm_nonneg x) hx 2
  have happ := (hb (star x * x)).trans (mul_le_mul_of_nonneg_left hsq hα.le)
  rw [he] at happ
  have ht := (trace_positive_square_functional_le τ b x).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx (norm_nonneg b))
      (traceTwoNorm_nonneg τ x))
  have hreal : ‖ρ x z‖ ^ 2 ≤ α * C ^ 2 + ‖b‖ * C * traceTwoNorm τ x := by
    have hr := Complex.re_le_norm (inner ℂ z (ρ (star x * x) z) -
      τ.toLinearMap (b * (star x * x)))
    rw [he, Complex.sub_re, Complex.ofReal_re] at hr
    have hrt := Complex.re_le_norm (τ.toLinearMap (b * (star x * x)))
    linarith
  have hαeq : α * (4 * (C ^ 2 + 1)) = ε ^ 2 := by
    dsimp [α]
    exact div_mul_cancel₀ _ (by positivity)
  have hηeq : η * (4 * (‖b‖ * (C + 1) + 1)) = ε ^ 2 := by
    dsimp [η]
    exact div_mul_cancel₀ _ (by positivity)
  have hsmall : ‖b‖ * C * traceTwoNorm τ x ≤ ‖b‖ * C * η :=
    mul_le_mul_of_nonneg_left hx2.le (mul_nonneg (norm_nonneg b) hC)
  have ha_bound : α * C ^ 2 < ε ^ 2 / 4 := by nlinarith
  have he_bound : ‖b‖ * C * η < ε ^ 2 / 4 := by
    have hb0 := norm_nonneg b
    nlinarith
  have hnorm0 := norm_nonneg (ρ x z)
  nlinarith

end

end KadisonKastler

end OAI
