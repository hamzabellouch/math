import OAI.Analysis.KadisonKastler.ModularProductTest

namespace OAI

/-! # The centered test as a commutator-energy difference -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularConjugationData

variable (d : ModularConjugationData M Ω)

theorem rightAction_conjugation (a : Algebra M) (ξ : H) :
    d.rightAction (star a) (d.conjugation ξ)=d.conjugation (a.val ξ) := by
  change d.conjugation (star (star a).val (d.conjugation (d.conjugation ξ)))=_
  simp only [StarMemClass.coe_star,star_star]
  rw [d.involutive]

theorem left_conjugation (a : Algebra M) (ξ : H) :
    a.val (d.conjugation ξ)=d.conjugation (d.rightAction (star a) ξ) := by
  have h := congrArg d.conjugation (d.rightAction_conjugation a (d.conjugation ξ))
  rw [d.involutive,d.involutive] at h
  exact h.symm

theorem centeredDefect_conjugation (a : Algebra M) (ξ : H) :
    a.val (d.conjugation ξ)-d.rightAction (star a) (d.conjugation ξ)=
      -d.conjugation (a.val ξ-d.rightAction (star a) ξ) := by
  rw [d.left_conjugation,d.rightAction_conjugation,map_sub]
  abel

theorem centeredDefect_algebra (a b : Algebra M)
    (ha : a.val Ω=d.rightAction (star a) Ω) :
    a.val (b.val Ω)-d.rightAction (star a) (b.val Ω)=(a*b-b*a).val Ω := by
  have hc := congrArg (fun T : H →L[ℂ] H => T Ω) (d.rightAction_commute b (star a))
  change b.val (d.rightAction (star a) Ω)=d.rightAction (star a) (b.val Ω) at hc
  rw [← hc,← ha]
  rfl

end ModularConjugationData

theorem modularCenteredTest_quadratic (d : ModularConjugationData M Ω)
    (a : Algebra M) (ξ : H) :
    (inner ℂ ξ (modularCenteredTest d a ξ)).re=
      ‖a.val ξ-d.rightAction (star a) ξ‖^2-‖d.rightAction (star a) ξ‖^2 := by
  change (inner ℂ ξ ((star (a.val-d.rightAction (star a))*(a.val-d.rightAction (star a))-
    star (d.rightAction (star a))*d.rightAction (star a)) ξ)).re=_
  rw [sub_apply,inner_sub_right,Complex.sub_re,mul_apply_eq_comp,mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right]
  change RCLike.re (inner ℂ ((a.val-d.rightAction (star a)) ξ)
    ((a.val-d.rightAction (star a)) ξ))-
      RCLike.re (inner ℂ (d.rightAction (star a) ξ) (d.rightAction (star a) ξ))=_
  rw [inner_self_eq_norm_sq,inner_self_eq_norm_sq]
  rfl

theorem modularCenteredTest_left_energy (d : ModularConjugationData M Ω)
    (a b : Algebra M) (ha : a.val Ω=d.rightAction (star a) Ω) :
    (inner ℂ (b.val Ω) (modularCenteredTest d a (b.val Ω))).re=
      ‖(a*b-b*a).val Ω‖^2-‖(b*a).val Ω‖^2 := by
  rw [modularCenteredTest_quadratic,d.centeredDefect_algebra a b ha]
  congr 2
  have hc := congrArg (fun T : H →L[ℂ] H => T Ω) (d.rightAction_commute b (star a))
  change b.val (d.rightAction (star a) Ω)=d.rightAction (star a) (b.val Ω) at hc
  rw [← hc,← ha]
  rfl

theorem modularCenteredTest_right_energy (d : ModularConjugationData M Ω)
    (a b : Algebra M) (ha : a.val Ω=d.rightAction (star a) Ω) :
    (inner ℂ (d.rightAction b Ω) (modularCenteredTest d a (d.rightAction b Ω))).re=
      ‖(a*star b-star b*a).val Ω‖^2-‖(a*star b).val Ω‖^2 := by
  have hr : d.rightAction b Ω=d.conjugation ((star b).val Ω) := by
    change d.conjugation (star b.val (d.conjugation Ω))=_
    rw [d.fixes_vector]
    rfl
  rw [modularCenteredTest_quadratic,hr,d.centeredDefect_conjugation,norm_neg,
    d.conjugation.norm_map,d.rightAction_conjugation,d.conjugation.norm_map,
    d.centeredDefect_algebra a (star b) ha]
  rfl

end

end KadisonKastler

end OAI
