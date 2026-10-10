import OAI.Analysis.KadisonKastler.ProjectionNormDecomposition

namespace OAI

/-! # The energy removed by a two-sided projection cut

For commuting left and right projections, the diagonal cut is an
orthogonal projection. Its discarded squared norm is exactly the
squared norm of their difference acting on the vector.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def pairedProjectionCut (p q : H →L[ℂ] H) : H →L[ℂ] H :=
  p * q + (1 - p) * (1 - q)

theorem pairedProjectionCut_isProjection {p q : H →L[ℂ] H}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : Commute p q) :
    IsStarProjection (pairedProjectionCut p q) := by
  have hc₁ : Commute (1 - p) q := (Commute.one_left q).sub_left hc
  have hc₂ : Commute (1 - p) (1 - q) := (Commute.one_right _).sub_right hc₁
  apply (hp.mul hq hc).add (hp.one_sub.mul hq.one_sub hc₂)
  calc
    (p * q) * ((1 - p) * (1 - q)) =
        p * (q * (1 - p)) * (1 - q) := by simp only [mul_assoc]
    _ = (p * (1 - p)) * (q * (1 - q)) := by rw [← hc₁.eq]; simp only [mul_assoc]
    _ = 0 := by rw [hp.mul_one_sub_self,zero_mul]

theorem pairedProjectionCut_complement {p q : H →L[ℂ] H}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : Commute p q) :
    (p - q) * (p - q) = 1 - pairedProjectionCut p q := by
  simp only [pairedProjectionCut,mul_sub,sub_mul,mul_one,one_mul,
    hp.isIdempotentElem.eq,hq.isIdempotentElem.eq,← hc.eq]
  abel

theorem pairedProjectionCut_discarded_norm {p q : H →L[ℂ] H}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : Commute p q) (ξ : H) :
    ‖(1 - pairedProjectionCut p q) ξ‖ = ‖(p - q) ξ‖ := by
  let C := 1 - pairedProjectionCut p q
  let D := p - q
  have hC : IsStarProjection C := (pairedProjectionCut_isProjection hp hq hc).one_sub
  have hD : IsSelfAdjoint D := hp.isSelfAdjoint.sub hq.isSelfAdjoint
  have hsC : C.adjoint = C := hC.isSelfAdjoint.star_eq
  have hsD : D.adjoint = D := hD.star_eq
  have hsq : ‖C ξ‖ ^ 2 = ‖D ξ‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ),norm_sq_eq_re_inner (𝕜 := ℂ),← C.adjoint_inner_right,
      ← D.adjoint_inner_right,hsC,hsD]
    change (inner ℂ ξ ((C * C) ξ)).re = (inner ℂ ξ ((D * D) ξ)).re
    rw [hC.isIdempotentElem.eq]
    exact congrArg (fun T : H →L[ℂ] H => (inner ℂ ξ (T ξ)).re)
      (pairedProjectionCut_complement hp hq hc).symm
  change ‖C ξ‖ = ‖D ξ‖
  nlinarith [norm_nonneg (C ξ),norm_nonneg (D ξ)]

theorem pairedProjectionCut_energy {p q : H →L[ℂ] H}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : Commute p q) (ξ : H) :
    ‖pairedProjectionCut p q ξ‖ ^ 2 + ‖(p - q) ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
  have h := projection_norm_sq_decomposition (pairedProjectionCut_isProjection hp hq hc) ξ
  rwa [pairedProjectionCut_discarded_norm hp hq hc] at h

end

end KadisonKastler

end OAI
