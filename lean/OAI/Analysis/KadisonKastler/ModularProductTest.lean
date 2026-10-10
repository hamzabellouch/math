import OAI.Analysis.KadisonKastler.ModularProductState
import OAI.Analysis.KadisonKastler.ModularRightAction

namespace OAI

/-! # The centered separating test for the bicentralizer criterion

These are the exact product-state moments used in Marrakchi,
arXiv:1811.10253v2, proof of Theorem D. The test has expectation one.
The approximate-eigenstate selection needed after this computation is separate.
-/

namespace KadisonKastler

open NaimarkZFC

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularConjugationData

variable (d : ModularConjugationData M Ω)

theorem rightAction_vectorState (a : Algebra M) :
    productVectorState Ω (d.rightAction a)=productVectorState Ω a.val := by
  change inner ℂ Ω (d.conjugation (star a.val (d.conjugation Ω)))=_
  rw [d.fixes_vector]
  have h := conjugateIsometry_inner d.conjugation Ω (star a.val Ω)
  rw [d.fixes_vector] at h
  rw [h,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  exact inner_conj_symm _ _

end ModularConjugationData

private theorem vectorState_square_value (a : H →L[ℂ] H) :
    productVectorState Ω (star a*a)=((‖a Ω‖^2 : ℝ) : ℂ) := by
  change inner ℂ Ω (star a (a Ω))=_
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  simp only [inner_self_eq_norm_sq_to_K,Complex.ofReal_pow]
  rfl

private theorem vectorState_star_value (a : H →L[ℂ] H) :
    productVectorState Ω (star a)=star (productVectorState Ω a) := by
  change inner ℂ Ω (star a Ω)=star (inner ℂ Ω (a Ω))
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm _ _).symm

def modularCenteredTest (d : ModularConjugationData M Ω) (a : Algebra M) : H →L[ℂ] H :=
  let R := d.rightAction (star a)
  star (a.val-R)*(a.val-R)-star R*R

theorem modularCenteredTest_selfAdjoint (d : ModularConjugationData M Ω) (a : Algebra M) :
    IsSelfAdjoint (modularCenteredTest d a) :=
  (IsSelfAdjoint.star_mul_self _).sub (IsSelfAdjoint.star_mul_self _)

theorem modularCenteredTest_product_value (d : ModularConjugationData M Ω)
    (hunit : ‖Ω‖=1) (ψ : (H →L[ℂ] H) →L[ℂ] ℂ)
    (hprod : ∀ a ∈ M, ∀ b ∈ M.commutant,
      ψ (a*b)=productVectorState Ω a*productVectorState Ω b)
    (a : Algebra M) (hzero : productVectorState Ω a.val=0) (hnorm : ‖a.val Ω‖=1) :
    ψ (modularCenteredTest d a)=1 := by
  have hone : productVectorState Ω (1 : H →L[ℂ] H)=1 := by
    change inner ℂ Ω Ω=1
    rw [inner_self_eq_norm_sq_to_K,hunit]
    norm_num
  have hleft : ψ (star a.val*a.val)=1 := by
    have h := hprod _ (M.mul_mem (M.toStarSubalgebra.star_mem' a.property) a.property)
      1 M.commutant.one_mem
    rw [mul_one,hone,mul_one,vectorState_square_value,hnorm] at h
    simpa using h
  have hcross : ψ (star a.val*d.rightAction (star a))=0 := by
    rw [hprod _ (M.toStarSubalgebra.star_mem' a.property) _ (d.rightAction_mem _),
      vectorState_star_value,hzero,star_zero,zero_mul]
  have hcross' : ψ (star (d.rightAction (star a))*a.val)=0 := by
    rw [← d.rightAction_star]
    have hc := d.rightAction_commute a (star (star a))
    rw [← hc,hprod _ a.property _ (d.rightAction_mem _),hzero,zero_mul]
  have hexpand : modularCenteredTest d a=
      star a.val*a.val-star a.val*d.rightAction (star a)-
        star (d.rightAction (star a))*a.val := by
    change star (a.val-d.rightAction (star a))*(a.val-d.rightAction (star a))-
      star (d.rightAction (star a))*d.rightAction (star a)=_
    rw [star_sub,sub_mul,mul_sub,mul_sub]
    abel
  rw [hexpand,map_sub,map_sub,hleft,hcross,hcross',sub_zero,sub_zero]

end

end KadisonKastler

end OAI
