import OAI.Analysis.FiniteFactor.Convolution
import OAI.Analysis.FiniteFactor.Fiber.ProjectionDiagonal

namespace OAI

namespace FiniteFactor
open scoped ComplexConjugate
noncomputable section

/-- Composition of the two genuine range inclusions used in the convolution. -/
theorem invariant_transport_composition {R : Type*} [Ring R] (P Q D W : R)
    (hD : (1-Q)*D*P = 0) (hW : (1-Q)*W*Q = 0) :
    (1-Q)*W*D*P = 0 := by
  have hd : D*P = Q*D*P := by
    apply sub_eq_zero.mp
    simpa only [sub_mul,one_mul] using hD
  calc
    _ = (1-Q)*W*(D*P) := by simp only [mul_assoc]
    _ = (1-Q)*W*(Q*D*P) := by rw [hd]
    _ = ((1-Q)*W*Q)*D*P := by simp only [mul_assoc]
    _ = 0 := by rw [hW,zero_mul,zero_mul]

theorem fiber_complement_inner_zero
    (Q : SourceFiberHilbert →L[ℂ] SourceFiberHilbert) (hQ : IsStarProjection Q)
    (u v : SourceFiberHilbert) (hv : (1-Q) v = 0) :
    inner ℂ ((1-Q) u) v = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right (1-Q) u v,
    ← ContinuousLinearMap.star_eq_adjoint,hQ.one_sub.isSelfAdjoint.star_eq,hv,inner_zero_right]

/-- The source convolution vanishes whenever the actual transport and weighted
power identities hold. No square summability of rescaled coefficients is assumed. -/
theorem fiber_transport_convolution_zero
    (P Q D W : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (hQ : IsStarProjection Q) (F G : ℤ → ℝ) (hG : ∀ k, G k ≠ 0) (n : ℤ)
    (hD : (1-Q)*D*P = 0) (hW : (1-Q)*W*Q = 0)
    (hDa : ∀ (v : SourceFiberHilbert) (k : ℤ), D v k = (G k / F k : ℂ) * v k)
    (hWa : ∀ (v : SourceFiberHilbert) (k : ℤ), W v (n+k) = (G (n+k) / G k : ℂ) * v k) :
    (∑' k, leftCoefficient F (P (lp.single 2 0 (1 : ℂ))) k *
      rightCoefficient G ((1-Q) (lp.single 2 0 (1 : ℂ))) (-n-k)) = 0 := by
  let ξ := P (lp.single 2 0 (1 : ℂ))
  let γ := (1-Q) (lp.single 2 0 (1 : ℂ))
  let η := W (D ξ)
  have hη : ∀ k, η (n+k) = ((G (n+k) / F k : ℝ) : ℂ) * ξ k := by
    intro k
    dsimp [η]
    rw [hWa,hDa,Complex.ofReal_div]
    have hg : (G k : ℂ) ≠ 0 := by exact_mod_cast hG k
    field_simp
  have hz : (1-Q) η = 0 := by
    exact congrArg (fun A : SourceFiberHilbert →L[ℂ] SourceFiberHilbert => A (lp.single 2 0 (1 : ℂ)))
      (invariant_transport_composition P Q D W hD hW)
  simp only [cocycle_convolution_term_eq]
  rw [weighted_shift_convolution_eq_inner ξ γ η (fun k => G (n+k)/F k) n hη]
  exact fiber_complement_inner_zero Q hQ _ η hz

end
end FiniteFactor

end OAI
