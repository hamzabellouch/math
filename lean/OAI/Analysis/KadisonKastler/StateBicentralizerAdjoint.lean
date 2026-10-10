import OAI.Analysis.KadisonKastler.StateOrbitBicentralizer

namespace OAI

/-! # Adjoint stability of state-sequence bicentralizers

Approximate preservation of the faithful state supplies the extra norm
control needed to pass from strong convergence to adjoint convergence.
-/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem adjoint_vector_difference_sq_le (ξ : H) (a b : H →L[ℂ] H) (R : ℝ)
    (hb : ‖b.adjoint ξ‖^2 ≤ ‖a.adjoint ξ‖^2+R) :
    ‖b.adjoint ξ-a.adjoint ξ‖^2 ≤ R+2*‖ξ‖*‖(b-a) (a.adjoint ξ)‖ := by
  let α := a.adjoint ξ
  let β := b.adjoint ξ
  have hself : (inner ℂ α α).re=‖α‖^2 := by
    rw [← RCLike.re_eq_complex_re,← norm_sq_eq_re_inner (𝕜 := ℂ)]
  have hc : (inner ℂ ξ ((b-a) α)).re=(inner ℂ β α).re-‖α‖^2 := by
    change (inner ℂ ξ (b α-a α)).re=_
    rw [inner_sub_right,Complex.sub_re,← b.adjoint_inner_left,← a.adjoint_inner_left]
    exact congrArg ((inner ℂ β α).re-·) hself
  have hs := norm_sub_sq (𝕜 := ℂ) β α
  change ‖β-α‖^2=‖β‖^2-2*(inner ℂ β α).re+‖α‖^2 at hs
  have hr : -(inner ℂ ξ ((b-a) α)).re ≤ ‖ξ‖*‖(b-a) α‖ :=
    (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _))
  change ‖β-α‖^2 ≤ _
  change ‖β‖^2 ≤ ‖α‖^2+R at hb
  nlinarith only [hc,hs,hr,hb]

theorem stateConjugate_adjoint_difference_sq_le (ξ : H) (a : Algebra M)
    (u : unitary (Algebra M)) :
    ‖(star (star u.val*a*u.val)-star a).val ξ‖^2 ≤
      ‖vectorStateCommutator ξ u.val‖*‖a‖^2+
        2*‖ξ‖*‖(star u.val*a*u.val-a).val ((star a).val ξ)‖ := by
  have hs (x : Algebra M) : x.val.adjoint=(star x).val := by
    rw [StarMemClass.coe_star,ContinuousLinearMap.star_eq_adjoint]
  have hb := stateConjugate_vector_norm_sq_le ξ (star a) u
  have h := adjoint_vector_difference_sq_le ξ a.val (star u.val*a*u.val).val
    (‖vectorStateCommutator ξ u.val‖*‖a‖^2) (by
      rw [hs,hs]
      simpa only [star_mul,star_star,mul_assoc,norm_star] using hb)
  rw [hs,hs] at h
  exact h

end

end KadisonKastler

end OAI
