import Mathlib
import OAI.Analysis.Commutator.TracialCommutation

namespace OAI

noncomputable section

section

open scoped ComplexOrder InnerProductSpace

open Complex ContinuousLinearMap UniformSpace Completion

noncomputable section

namespace Kadison.TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

lemma operatorConjugate_mul (T R : τ.GNS →L[ℂ] τ.GNS) :
    operatorConjugate τ hτ (T*R)=operatorConjugate τ hτ T*operatorConjugate τ hτ R := by
  ext x
  simp only [operatorConjugate_apply,mul_apply_eq_comp,starMap_starMap]

lemma operatorConjugate_norm_le (T : τ.GNS →L[ℂ] τ.GNS) :
    ‖operatorConjugate τ hτ T‖≤‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  simp only [operatorConjugate_apply,starMap_norm]
  exact (T.le_opNorm _).trans_eq (by rw [starMap_norm])

lemma operatorConjugate_norm (T : τ.GNS →L[ℂ] τ.GNS) :
    ‖operatorConjugate τ hτ T‖=‖T‖ := by
  apply le_antisymm (operatorConjugate_norm_le τ hτ T)
  have h := operatorConjugate_norm_le τ hτ (operatorConjugate τ hτ T)
  rw [operatorConjugate_involutive τ hτ T] at h
  exact h

lemma operatorConjugate_left (a : A) :
    operatorConjugate τ hτ (τ.gnsStarAlgHom a)=rightMul τ hτ (star a) := by
  apply ContinuousLinearMap.ext
  have he : ∀ b : A, operatorConjugate τ hτ (τ.gnsStarAlgHom a) (algebraVector τ b)=
      rightMul τ hτ (star a) (algebraVector τ b) := by
    intro b
    rw [operatorConjugate_apply,starMap_algebra]
    change starMap τ hτ (τ.gnsStarAlgHom a (τ.toPreGNS (star b) : τ.GNS))=_
    rw [left_coe]
    change starMap τ hτ (algebraVector τ (a*star b))=rightMul τ hτ (star a) (τ.toPreGNS b : τ.GNS)
    rw [starMap_algebra,rightMul_coe]
    simp only [star_mul,star_star,PositiveLinearMap.ofPreGNS_toPreGNS,algebraVector_apply]
  exact fun x => congrFun ((algebraVector_dense τ).equalizer
    (operatorConjugate τ hτ (τ.gnsStarAlgHom a)).continuous
    (rightMul τ hτ (star a)).continuous (funext he)) x

lemma operatorConjugate_right (a : A) :
    operatorConjugate τ hτ (rightMul τ hτ a)=τ.gnsStarAlgHom (star a) := by
  have h := congrArg (operatorConjugate τ hτ) (operatorConjugate_left τ hτ (star a))
  simpa only [operatorConjugate_involutive τ hτ _,star_star] using h.symm

lemma bicommutant_star {T : τ.GNS →L[ℂ] τ.GNS}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range τ.gnsStarAlgHom))) :
    star T∈Set.centralizer (Set.centralizer (Set.range τ.gnsStarAlgHom)) := by
  intro R hR
  have h := congrArg star (hT _ (commutant_star τ hR))
  simpa only [star_mul,star_star] using h.symm

lemma operatorConjugate_bicommutant_mem_commutant {T : τ.GNS →L[ℂ] τ.GNS}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range τ.gnsStarAlgHom))) :
    operatorConjugate τ hτ T∈Set.centralizer (Set.range τ.gnsStarAlgHom) := by
  rintro _ ⟨a,rfl⟩
  have h := congrArg (operatorConjugate τ hτ)
    (hT _ (rightMul_mem_commutant τ hτ (star a)))
  simpa only [operatorConjugate_mul,operatorConjugate_right,star_star] using h

def rightOperator (T : τ.GNS →L[ℂ] τ.GNS) : τ.GNS →L[ℂ] τ.GNS :=
  operatorConjugate τ hτ (star T)

lemma rightOperator_original (a : A) :
    rightOperator τ hτ (τ.gnsStarAlgHom a)=rightMul τ hτ a := by
  rw [rightOperator,←map_star,operatorConjugate_left,star_star]

lemma rightOperator_norm (T : τ.GNS →L[ℂ] τ.GNS) : ‖rightOperator τ hτ T‖=‖T‖ := by
  rw [rightOperator,operatorConjugate_norm]
  exact ContinuousLinearMap.adjoint.norm_map T

lemma rightOperator_mul (T R : τ.GNS →L[ℂ] τ.GNS) :
    rightOperator τ hτ (T*R)=rightOperator τ hτ R*rightOperator τ hτ T := by
  rw [rightOperator,star_mul,operatorConjugate_mul]
  rfl

theorem commutation {T : τ.GNS →L[ℂ] τ.GNS}
    (hT : T∈Set.centralizer (Set.range τ.gnsStarAlgHom)) :
    ∃ b : τ.GNS →L[ℂ] τ.GNS,
      b∈Set.centralizer (Set.centralizer (Set.range τ.gnsStarAlgHom)) ∧
      T=rightOperator τ hτ b ∧ ‖b‖=‖T‖ := by
  refine ⟨star (operatorConjugate τ hτ T),
    bicommutant_star τ (operatorConjugate_commutant_mem_bicommutant τ hτ hT),?_,?_⟩
  · simp only [rightOperator,star_star]
    exact (operatorConjugate_involutive τ hτ T).symm
  · change ‖ContinuousLinearMap.adjoint (operatorConjugate τ hτ T)‖=‖T‖
    rw [ContinuousLinearMap.adjoint.norm_map,operatorConjugate_norm]

lemma starMap_bicommutant_vacuum {T : τ.GNS →L[ℂ] τ.GNS}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range τ.gnsStarAlgHom))) :
    starMap τ hτ (T (vacuum τ))=star T (vacuum τ) := by
  apply (algebraVector_dense τ).eq_of_inner_right ℂ
  intro a
  have hc : rightMul τ hτ a (T (vacuum τ))=T (algebraVector τ a) := by
    have he := congrArg (fun V : τ.GNS →L[ℂ] τ.GNS => V (vacuum τ))
      (hT _ (rightMul_mem_commutant τ hτ a))
    simpa only [mul_apply_eq_comp,right_vacuum,algebraVector_apply] using he
  calc
    _ = inner ℂ (T (vacuum τ)) (starMap τ hτ (algebraVector τ a)) := by
      simpa only [starMap_starMap] using
        (starMap_inner τ hτ (starMap τ hτ (algebraVector τ a)) (T (vacuum τ)))
    _ = inner ℂ (T (vacuum τ)) (rightMul τ hτ (star a) (vacuum τ)) := by
      rw [starMap_algebra,right_vacuum]; rfl
    _ = inner ℂ (rightMul τ hτ a (T (vacuum τ))) (vacuum τ) := by
      rw [rightMul_star,ContinuousLinearMap.adjoint_inner_right]
    _ = inner ℂ (T (algebraVector τ a)) (vacuum τ) := by rw [hc]
    _ = inner ℂ (algebraVector τ a) (star T (vacuum τ)) := by
      rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]

include hτ in
lemma bicommutant_vacuum_separating {T : τ.GNS →L[ℂ] τ.GNS}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range τ.gnsStarAlgHom)))
    (hz : T (vacuum τ)=0) : T=0 := by
  apply ContinuousLinearMap.ext
  have he : ∀ a : A, T (algebraVector τ a)=0 := by
    intro a
    have hh := congrArg (fun V : τ.GNS →L[ℂ] τ.GNS => V (vacuum τ))
      (hT _ (rightMul_mem_commutant τ hτ a))
    simpa only [mul_apply_eq_comp,right_vacuum,algebraVector_apply,hz,map_zero] using hh.symm
  exact fun x => congrFun ((algebraVector_dense τ).equalizer T.continuous continuous_const (funext he)) x

include hτ in
lemma bicommutant_trace {T R : τ.GNS →L[ℂ] τ.GNS}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range τ.gnsStarAlgHom)))
    (hR : R∈Set.centralizer (Set.centralizer (Set.range τ.gnsStarAlgHom))) :
    inner ℂ (vacuum τ) ((T*R) (vacuum τ))=
      inner ℂ (vacuum τ) ((R*T) (vacuum τ)) := by
  calc
    _ = inner ℂ (star T (vacuum τ)) (R (vacuum τ)) := by
      rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
      rfl
    _ = inner ℂ (starMap τ hτ (T (vacuum τ))) (R (vacuum τ)) := by
      rw [starMap_bicommutant_vacuum τ hτ hT]
    _ = inner ℂ (starMap τ hτ (R (vacuum τ))) (T (vacuum τ)) := by
      simpa only [starMap_starMap] using
        (starMap_inner τ hτ (T (vacuum τ)) (starMap τ hτ (R (vacuum τ))))
    _ = inner ℂ (star R (vacuum τ)) (T (vacuum τ)) := by
      rw [starMap_bicommutant_vacuum τ hτ hR]
    _ = _ := by
      rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
      rfl

end Kadison.TracialGNS

end

end
end

end OAI
