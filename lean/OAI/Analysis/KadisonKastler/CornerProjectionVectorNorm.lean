import OAI.Analysis.KadisonKastler.FiniteProjectionVectorCriterion

namespace OAI

/-! # Equivalent projections in a corner with a tracial vector norm -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

private theorem vector_norm_sq (a : H →L[ℂ] H) (ξ : H) :
    ‖a ξ‖ ^ 2 = (inner ℂ ξ ((star a * a) ξ)).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact congrArg Complex.re (ContinuousLinearMap.adjoint_inner_right a ξ (a ξ)).symm

theorem equivalent_corner_projection_vector_norm
    (p q r : AlgebraProjection M) (ξ : H) (hq : q ≤ p) (hr : r ≤ p)
    (htrace : ∀ a : Algebra M, p.val * a = a → a * p.val = a →
      ‖a.val ξ‖ = ‖(star a).val ξ‖) (heq : q.Equivalent r) :
    ‖q.val.val ξ‖ = ‖r.val.val ξ‖ := by
  obtain ⟨v, hvq, hvr⟩ := heq
  have hvp : v.val * p.val = v.val :=
    (v.support_le_iff_mul p).mp (hvq ▸ hq)
  have hpv : p.val * v.val = v.val :=
    (v.target_le_iff_mul p).mp (hvr ▸ hr)
  have hnorm := htrace v.val hpv hvp
  have hi : star v.val.val * v.val.val = q.val.val := by
    exact congrArg Subtype.val (v.initial.trans (congrArg Subtype.val hvq))
  have ht : v.val.val * star v.val.val = r.val.val := by
    exact congrArg (fun x : AlgebraProjection M => x.val.val) hvr
  have hqnorm : ‖v.val.val ξ‖ ^ 2 = ‖q.val.val ξ‖ ^ 2 := by
    rw [vector_norm_sq, hi, vector_norm_sq]
    have hqq : star q.val * q.val = q.val := by
      rw [q.property.isSelfAdjoint.star_eq, q.property.isIdempotentElem.eq]
    have he : star q.val.val * q.val.val = q.val.val := by
      exact congrArg Subtype.val hqq
    rw [he]
  have hrnorm : ‖(star v.val).val ξ‖ ^ 2 = ‖r.val.val ξ‖ ^ 2 := by
    rw [vector_norm_sq, vector_norm_sq]
    change (inner ℂ ξ ((star (star v.val.val) * star v.val.val) ξ)).re = _
    rw [star_star, ht]
    have hrr : star r.val * r.val = r.val := by
      rw [r.property.isSelfAdjoint.star_eq, r.property.isIdempotentElem.eq]
    have he : star r.val.val * r.val.val = r.val.val := by
      exact congrArg Subtype.val hrr
    rw [he]
  have hs := congrArg (fun t : ℝ => t ^ 2) hnorm
  change ‖v.val.val ξ‖ ^ 2 = ‖(star v.val).val ξ‖ ^ 2 at hs
  rw [hqnorm, hrnorm] at hs
  nlinarith [norm_nonneg (q.val.val ξ), norm_nonneg (r.val.val ξ)]

end

end KadisonKastler

end OAI
