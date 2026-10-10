import OAI.Analysis.KadisonKastler.SymmetricVectorAngle
import OAI.Analysis.KadisonKastler.ProjectionNormDecomposition

namespace OAI

/-! # A uniform angle bound in a nearly full Hilbert corner

A projection which loses little of two orthogonal unit vectors keeps
both vectors nonzero and keeps their normalized angle away from zero.
The determinant estimate avoids introducing trigonometric functions.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem projection_corner_inner_bound {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (ξ η : H) (hη : ‖η‖=1) (horth : inner ℂ ξ η=0) :
    ‖inner ℂ (P ξ) (P η)‖ ≤ ‖(1-P) ξ‖ := by
  have hs : P.adjoint=P := hP.isSelfAdjoint.star_eq
  have he : inner ℂ (P ξ) (P η)= -(inner ℂ ((1-P) ξ) η) := by
    rw [← P.adjoint_inner_right,hs]
    change inner ℂ ξ ((P*P) η)=_
    rw [hP.isIdempotentElem.eq]
    have hh : inner ℂ ((1-P) ξ) η = inner ℂ ξ η-inner ℂ (P ξ) η := by
      change inner ℂ (ξ-P ξ) η=_
      rw [inner_sub_left]
    rw [hh,horth]
    have ht := P.adjoint_inner_right ξ η
    rw [hs] at ht
    simpa only [zero_sub,neg_neg] using ht
  rw [he,norm_neg]
  simpa only [hη,mul_one] using norm_inner_le_norm ((1-P) ξ) η

theorem projection_corner_angle_determinant {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (ξ η : H) (hξ : ‖ξ‖=1) (hη : ‖η‖=1)
    (horth : inner ℂ ξ η=0)
    (hsmall : ‖(1-P) ξ‖^2+‖(1-P) η‖^2 ≤ 1/16) :
    0 < ‖P ξ‖ ∧ 0 < ‖P η‖ ∧
      1/2 ≤ ‖P ξ‖^2*‖P η‖^2-(inner ℂ (P ξ) (P η)).re^2 := by
  have hx := projection_norm_sq_decomposition hP ξ
  have hy := projection_norm_sq_decomposition hP η
  rw [hξ] at hx
  rw [hη] at hy
  have hb := (Complex.abs_re_le_norm (inner ℂ (P ξ) (P η))).trans
    (projection_corner_inner_bound hP ξ η hη horth)
  have hb2 := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hb
  rw [sq_abs] at hb2
  have hprod := mul_nonneg (sq_nonneg ‖(1-P) ξ‖) (sq_nonneg ‖(1-P) η‖)
  have hdet : 1/2 ≤ ‖P ξ‖^2*‖P η‖^2-(inner ℂ (P ξ) (P η)).re^2 := by
    nlinarith only [hx,hy,hsmall,hb2,hprod,sq_nonneg ‖(1-P) ξ‖,sq_nonneg ‖(1-P) η‖]
  refine ⟨?_,?_,hdet⟩
  · nlinarith only [hx,hsmall,sq_nonneg ‖(1-P) η‖,norm_nonneg (P ξ)]
  · nlinarith only [hy,hsmall,sq_nonneg ‖(1-P) ξ‖,norm_nonneg (P η)]

end

end KadisonKastler

end OAI
