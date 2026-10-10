import OAI.Analysis.KadisonKastler.ProjectionSemifiniteness

namespace OAI

/-! # Finiteness from the faithful tracial vector identity on a corner

Only the norm identity for elements of the indicated corner is needed.
This isolates the final projection argument from construction of the
core's tracial vector.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

private theorem operator_vector_norm_sq (a : H →L[ℂ] H) (ξ : H) :
    ‖a ξ‖ ^ 2 = (inner ℂ ξ ((star a * a) ξ)).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change (inner ℂ (a ξ) (a ξ)).re = (inner ℂ ξ ((star a * a) ξ)).re
  exact congrArg Complex.re (ContinuousLinearMap.adjoint_inner_right a ξ (a ξ)).symm

theorem finiteProjectionIn_of_faithful_vector_norm
    (p : AlgebraProjection M) (ξ : H) (hξ : p.val.val ξ = ξ)
    (hfaith : ∀ a : Algebra M, a.val ξ = 0 → a * p.val = 0)
    (htrace : ∀ a : Algebra M, p.val * a = a → a * p.val = a →
      ‖a.val ξ‖ = ‖(star a).val ξ‖) : FiniteProjectionIn M p.val := by
  intro v hvi hpv
  let V : PartialIsometry M := ⟨p, v, hvi⟩
  have hq : V.target ≤ p := (V.target_le_iff_mul p).mpr hpv
  let r := AlgebraProjection.remainder V.target p hq
  have hrv : r.val = p.val - v * star v := rfl
  have hvp : v * p.val = v := V.mul_support
  have hvnorm : ‖v.val ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
    rw [operator_vector_norm_sq]
    have he : star v.val * v.val = p.val.val := congrArg Subtype.val hvi
    rw [he, hξ, norm_sq_eq_re_inner (𝕜 := ℂ)]
    rfl
  have hvsnorm : ‖(star v).val ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
    rw [← htrace v hpv hvp]
    exact hvnorm
  have hrzero : r.val.val ξ = 0 := by
    have hrsq : ‖r.val.val ξ‖ ^ 2 = 0 := by
      rw [operator_vector_norm_sq]
      have hrs : star r.val * r.val = r.val := by
        rw [r.property.isSelfAdjoint.star_eq, r.property.isIdempotentElem.eq]
      have he : star r.val.val * r.val.val = r.val.val := congrArg Subtype.val hrs
      rw [he]
      change (inner ℂ ξ ((p.val.val - v.val * star v.val) ξ)).re = 0
      rw [sub_apply, hξ, inner_sub_right, Complex.sub_re]
      have hvstar := operator_vector_norm_sq (star v.val) ξ
      simp only [star_star] at hvstar
      rw [← hvstar]
      change RCLike.re (inner ℂ ξ ξ) - ‖(star v).val ξ‖ ^ 2 = 0
      rw [← norm_sq_eq_re_inner (𝕜 := ℂ), hvsnorm, sub_self]
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (r.val.val ξ)])
  have hrp : r.val * p.val = r.val := by
    have he := congrArg star (AlgebraProjection.remainder_le V.target p hq)
    change star (p.val * r.val) = star r.val at he
    simpa only [star_mul, p.property.isSelfAdjoint.star_eq,
      r.property.isSelfAdjoint.star_eq] using he
  have hr := hfaith r.val hrzero
  rw [hrp, hrv] at hr
  exact (sub_eq_zero.mp hr).symm

end

end KadisonKastler

end OAI
