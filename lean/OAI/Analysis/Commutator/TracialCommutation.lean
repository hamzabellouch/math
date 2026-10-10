import Mathlib
import OAI.Analysis.Commutator.TracialConjugation

namespace OAI

noncomputable section

section

open scoped ComplexOrder InnerProductSpace

open Complex ContinuousLinearMap UniformSpace Completion

namespace Kadison.TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))

noncomputable def starPre : τ.PreGNS →L⋆[ℂ] τ.PreGNS :=
  (τ.toPreGNS.toLinearMap.comp
    ((starLinearEquiv ℂ : A ≃ₗ⋆[ℂ] A).toLinearMap.comp τ.ofPreGNS.toLinearMap)).mkContinuous
    1 (fun x => by
      change ‖τ.toPreGNS (star (τ.ofPreGNS x))‖ ≤ 1 * ‖x‖
      rw [norm_star_preGNS τ hτ, PositiveLinearMap.toPreGNS_ofPreGNS, one_mul])

@[simp] lemma starPre_apply (x : τ.PreGNS) :
    starPre τ hτ x = τ.toPreGNS (star (τ.ofPreGNS x)) := rfl

noncomputable def starMap : τ.GNS →L⋆[ℂ] τ.GNS := (starPre τ hτ).completion

@[simp] lemma starMap_algebra (a : A) :
    starMap τ hτ (algebraVector τ a) = algebraVector τ (star a) := by
  simp only [algebraVector_apply, starMap, ContinuousLinearMap.completion_apply_coe,
    starPre_apply, PositiveLinearMap.ofPreGNS_toPreGNS]

lemma starMap_norm (x : τ.GNS) : ‖starMap τ hτ x‖ = ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih a =>
    change ‖starMap τ hτ (algebraVector τ (τ.ofPreGNS a))‖ = ‖(a : τ.GNS)‖
    rw [starMap_algebra]
    simp only [algebraVector_apply, Completion.norm_coe, norm_star_preGNS τ hτ,
      PositiveLinearMap.toPreGNS_ofPreGNS]

lemma starMap_involutive : Function.Involutive (starMap τ hτ) := by
  intro x
  induction x using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih a =>
    change starMap τ hτ (starMap τ hτ (algebraVector τ (τ.ofPreGNS a))) = _
    rw [starMap_algebra, starMap_algebra, star_star]
    rfl

lemma starMap_inner (x y : τ.GNS) :
    inner ℂ (starMap τ hτ x) (starMap τ hτ y) = inner ℂ y x := by
  induction x, y using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih a b =>
    change inner ℂ (starMap τ hτ (algebraVector τ (τ.ofPreGNS a)))
      (starMap τ hτ (algebraVector τ (τ.ofPreGNS b))) = _
    rw [starMap_algebra, starMap_algebra, inner_algebraVector, star_star, hτ]
    simp only [Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]

@[simp] lemma starMap_vacuum : starMap τ hτ (vacuum τ) = vacuum τ := by
  change starMap τ hτ (algebraVector τ 1) = _
  rw [starMap_algebra, star_one]
  rfl

@[simp] lemma starMap_starMap (x : τ.GNS) : starMap τ hτ (starMap τ hτ x)=x :=
  starMap_involutive τ hτ x

noncomputable def operatorConjugate (T : τ.GNS →L[ℂ] τ.GNS) : τ.GNS →L[ℂ] τ.GNS :=
  (starMap τ hτ).comp (T.comp (starMap τ hτ))

@[simp] lemma operatorConjugate_apply (T : τ.GNS →L[ℂ] τ.GNS) (x : τ.GNS) :
    operatorConjugate τ hτ T x=starMap τ hτ (T (starMap τ hτ x)) := rfl

lemma operatorConjugate_involutive : Function.Involutive (operatorConjugate τ hτ) := by
  intro T
  ext x
  simp only [operatorConjugate_apply,starMap_starMap]

lemma commutant_star {T : τ.GNS →L[ℂ] τ.GNS}
    (hT : T∈Set.centralizer (Set.range τ.gnsStarAlgHom)) :
    star T∈Set.centralizer (Set.range τ.gnsStarAlgHom) := by
  rintro _ ⟨a,rfl⟩
  have h := congrArg star (hT _ ⟨star a,rfl⟩)
  simpa only [star_mul,map_star,star_star] using h.symm

lemma starMap_commutant_vacuum {T : τ.GNS →L[ℂ] τ.GNS}
    (hT : T∈Set.centralizer (Set.range τ.gnsStarAlgHom)) :
    starMap τ hτ (T (vacuum τ))=star T (vacuum τ) := by
  apply (algebraVector_dense τ).eq_of_inner_right ℂ
  intro a
  have hc : τ.gnsStarAlgHom a (T (vacuum τ))=T (algebraVector τ a) := by
    have he := congrArg (fun V : τ.GNS →L[ℂ] τ.GNS => V (vacuum τ)) (hT _ ⟨a,rfl⟩)
    simpa only [mul_apply_eq_comp,left_vacuum,algebraVector_apply] using he
  calc
    _ = inner ℂ (T (vacuum τ)) (starMap τ hτ (algebraVector τ a)) := by
      simpa only [starMap_starMap] using
        (starMap_inner τ hτ (starMap τ hτ (algebraVector τ a)) (T (vacuum τ)))
    _ = inner ℂ (T (vacuum τ)) (τ.gnsStarAlgHom (star a) (vacuum τ)) := by
      rw [starMap_algebra,left_vacuum]; rfl
    _ = inner ℂ (τ.gnsStarAlgHom a (T (vacuum τ))) (vacuum τ) := by
      rw [map_star,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
    _ = inner ℂ (T (algebraVector τ a)) (vacuum τ) := by rw [hc]
    _ = inner ℂ (algebraVector τ a) (star T (vacuum τ)) := by
      rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]

lemma operatorConjugate_commutant_orbit {T R : τ.GNS →L[ℂ] τ.GNS}
    (hT : T∈Set.centralizer (Set.range τ.gnsStarAlgHom))
    (hR : R∈Set.centralizer (Set.range τ.gnsStarAlgHom)) :
    operatorConjugate τ hτ T (R (vacuum τ))=R (star T (vacuum τ)) := by
  rw [operatorConjugate_apply,starMap_commutant_vacuum τ hτ hR]
  change starMap τ hτ ((T*star R) (vacuum τ))=_
  rw [starMap_commutant_vacuum τ hτ (Set.mul_mem_centralizer hT (commutant_star τ hR)),star_mul,star_star]
  rfl

lemma rightMul_mem_commutant (a : A) :
    rightMul τ hτ a∈Set.centralizer (Set.range τ.gnsStarAlgHom) := by
  rintro _ ⟨b,rfl⟩
  exact left_right_commute τ hτ b a

theorem operatorConjugate_commutant_mem_bicommutant {T : τ.GNS →L[ℂ] τ.GNS}
    (hT : T∈Set.centralizer (Set.range τ.gnsStarAlgHom)) :
    operatorConjugate τ hτ T∈Set.centralizer (Set.centralizer (Set.range τ.gnsStarAlgHom)) := by
  intro R hR
  apply ContinuousLinearMap.ext
  have he : ∀ a : A, (R*operatorConjugate τ hτ T) (algebraVector τ a)=
      (operatorConjugate τ hτ T*R) (algebraVector τ a) := by
    intro a
    rw [←show rightMul τ hτ a (vacuum τ)=algebraVector τ a from right_vacuum τ hτ a]
    have ha := rightMul_mem_commutant τ hτ a
    change R (operatorConjugate τ hτ T (rightMul τ hτ a (vacuum τ)))=
      operatorConjugate τ hτ T ((R*rightMul τ hτ a) (vacuum τ))
    rw [operatorConjugate_commutant_orbit τ hτ hT ha,
      operatorConjugate_commutant_orbit τ hτ hT (Set.mul_mem_centralizer hR ha)]
    rfl
  exact fun x => congrFun ((algebraVector_dense τ).equalizer
    (R*operatorConjugate τ hτ T).continuous (operatorConjugate τ hτ T*R).continuous (funext he)) x

end Kadison.TracialGNS

end
end

end OAI
