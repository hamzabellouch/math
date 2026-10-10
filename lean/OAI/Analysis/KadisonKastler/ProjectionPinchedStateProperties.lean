import OAI.Analysis.KadisonKastler.ProjectionPinchedState

namespace OAI

/-! # Positivity and faithfulness of the pinched vector state -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem projectionPinchedState_star_mul_self (p : H →L[ℂ] H) (ξ : H) (x : Algebra M) :
    projectionPinchedState (M := M) p ξ (star x*x) =
      (‖x.val (p ξ)‖ ^ 2 + ‖x.val ((1-p) ξ)‖ ^ 2 : ℝ) := by
  change vectorFunctional (p ξ) (star x*x) + vectorFunctional ((1-p) ξ) (star x*x) = _
  rw [vectorFunctional_star_mul_self,vectorFunctional_star_mul_self]
  norm_cast

theorem projectionPinchedState_positive (p : H →L[ℂ] H) (ξ : H) (x : Algebra M) :
    0 ≤ (projectionPinchedState (M := M) p ξ (star x*x)).re := by
  rw [projectionPinchedState_star_mul_self,Complex.ofReal_re]
  positivity

theorem projectionPinchedState_one {p : H →L[ℂ] H} (hp : IsStarProjection p)
    (ξ : H) : projectionPinchedState (M := M) p ξ 1 = (‖ξ‖ ^ 2 : ℝ) := by
  change inner ℂ (p ξ) (p ξ) + inner ℂ ((1-p) ξ) ((1-p) ξ) = _
  rw [inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K]
  simp only [← RCLike.ofReal_pow,← RCLike.ofReal_add]
  exact congrArg (RCLike.ofReal : ℝ → ℂ) (projection_norm_sq_decomposition hp ξ)

theorem projectionPinchedState_faithful (p : H →L[ℂ] H) (ξ : H)
    (hξ : Function.Injective (fun a : Algebra M => a.val ξ))
    (x : Algebra M) (hx : projectionPinchedState (M := M) p ξ (star x*x) = 0) : x = 0 := by
  rw [projectionPinchedState_star_mul_self] at hx
  have hr : ‖x.val (p ξ)‖ ^ 2 + ‖x.val ((1-p) ξ)‖ ^ 2 = 0 := by exact_mod_cast hx
  have hp : x.val (p ξ) = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (x.val (p ξ))])
  have hq : x.val ((1-p) ξ) = 0 :=
    norm_eq_zero.mp (by nlinarith [norm_nonneg (x.val ((1-p) ξ))])
  apply hξ
  change x.val ξ = 0
  calc
    _ = x.val (p ξ + (1-p) ξ) := by simp only [sub_apply,one_apply_eq_self]; congr 1; abel
    _ = 0 := by rw [map_add,hp,hq,add_zero]

theorem projectionPinchedState_centralizes {p : H →L[ℂ] H}
    (hp : IsStarProjection p) (hpM : p ∈ M) (ξ : H) (x : Algebra M) :
    projectionPinchedState (M := M) p ξ (⟨p,hpM⟩*x) =
      projectionPinchedState (M := M) p ξ (x*⟨p,hpM⟩) := by
  have hpp : p (p ξ) = p ξ := congrArg (fun T : H →L[ℂ] H => T ξ) hp.isIdempotentElem.eq
  have hpq : p ((1-p) ξ) = 0 := by
    simp only [sub_apply,one_apply_eq_self,map_sub,hpp,sub_self]
  have hs : p.adjoint = p := hp.isSelfAdjoint.star_eq
  change inner ℂ (p ξ) (p (x.val (p ξ))) + inner ℂ ((1-p) ξ) (p (x.val ((1-p) ξ))) =
    inner ℂ (p ξ) (x.val (p (p ξ))) + inner ℂ ((1-p) ξ) (x.val (p ((1-p) ξ)))
  rw [← p.adjoint_inner_left,← p.adjoint_inner_left,hs,hpp,hpq,map_zero,inner_zero_right,
    inner_zero_left,add_zero]

theorem projectionPinchedState_norm_le {p : H →L[ℂ] H} (hp : IsStarProjection p) (ξ : H) :
    ‖projectionPinchedState (M := M) p ξ‖ ≤ ‖ξ‖ ^ 2 := by
  let u : unitary (H →L[ℂ] H) := ⟨projectionReflection p,projectionReflection_unitary hp⟩
  rw [projectionPinchedState_reflection,norm_smul]
  have ht := (norm_add_le (vectorFunctional (M := M) ξ)
    (vectorFunctional ((u : H →L[ℂ] H) ξ))).trans
      (add_le_add (vectorFunctional_norm_le ξ) (vectorFunctional_norm_le _))
  rw [Unitary.norm_map u] at ht
  have hm := mul_le_mul_of_nonneg_left ht (norm_nonneg (1/2:ℂ))
  change ‖(1/2:ℂ)‖ * ‖vectorFunctional ξ + vectorFunctional ((u : H →L[ℂ] H) ξ)‖ ≤ _
  exact hm.trans_eq (by norm_num; ring)

end

end KadisonKastler

end OAI
