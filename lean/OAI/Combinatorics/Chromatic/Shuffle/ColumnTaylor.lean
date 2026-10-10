import Mathlib
import OAI.Combinatorics.Chromatic.Walls.LaurentLinearNaturality
import OAI.Combinatorics.Chromatic.Shuffle.ShuffleProjection
import OAI.Combinatorics.Chromatic.Shuffle.FourColumns

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.CommonTranslation
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable local instance colTaylorTensorRing (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance colTaylorTensorAlg (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance colTaylorFourRing (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance
noncomputable local instance colTaylorFourAlg (d₁ e₁ d₂ e₂ : I → ℕ) :
    Algebra ℚ ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance

omit [Fintype I] [DecidableEq I] in
lemma translationS_one (d : I → ℕ) (t : ℚ) : translationS d t (1 : S d)=1 := by
  apply Subtype.ext
  exact map_one (translation t)

omit [Fintype I] [DecidableEq I] in
lemma firstColumn_relativeTaylor (d₁ e₁ d₂ e₂ : I → ℕ) (x : S d₁⊗[ℚ]S d₂) :
    Polynomial.map (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom (relativeTaylor d₁ d₂ x)=
      fourRelativeTaylor d₁ e₁ d₂ e₂ (firstColumnAlg d₁ e₁ d₂ e₂ x) := by
  apply polynomial_eq_of_rat_evals
  intro t
  rw [eval_map_rat,relativeTaylor_eval,fourRelativeTaylor_eval]
  have h : (firstColumnAlg d₁ e₁ d₂ e₂).toLinearMap ∘ₗ
      TensorProduct.map (translationS d₁ t) LinearMap.id=
      TensorProduct.map (TensorProduct.map (translationS d₁ t) (translationS e₁ t)) LinearMap.id ∘ₗ
        (firstColumnAlg d₁ e₁ d₂ e₂).toLinearMap := by
    apply TensorProduct.ext'
    intro u v
    change ((translationS d₁ t u)⊗ₜ[ℚ](1 : S e₁))⊗ₜ[ℚ](v⊗ₜ[ℚ](1 : S e₂))=
      ((translationS d₁ t u)⊗ₜ[ℚ](translationS e₁ t 1))⊗ₜ[ℚ](v⊗ₜ[ℚ](1 : S e₂))
    rw [translationS_one]
  exact LinearMap.congr_fun h x

omit [Fintype I] [DecidableEq I] in
lemma secondColumn_relativeTaylor (d₁ e₁ d₂ e₂ : I → ℕ) (x : S e₁⊗[ℚ]S e₂) :
    Polynomial.map (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom (relativeTaylor e₁ e₂ x)=
      fourRelativeTaylor d₁ e₁ d₂ e₂ (secondColumnAlg d₁ e₁ d₂ e₂ x) := by
  apply polynomial_eq_of_rat_evals
  intro t
  rw [eval_map_rat,relativeTaylor_eval,fourRelativeTaylor_eval]
  have h : (secondColumnAlg d₁ e₁ d₂ e₂).toLinearMap ∘ₗ
      TensorProduct.map (translationS e₁ t) LinearMap.id=
      TensorProduct.map (TensorProduct.map (translationS d₁ t) (translationS e₁ t)) LinearMap.id ∘ₗ
        (secondColumnAlg d₁ e₁ d₂ e₂).toLinearMap := by
    apply TensorProduct.ext'
    intro u v
    change ((1 : S d₁)⊗ₜ[ℚ](translationS e₁ t u))⊗ₜ[ℚ]((1 : S d₂)⊗ₜ[ℚ]v)=
      ((translationS d₁ t 1)⊗ₜ[ℚ](translationS e₁ t u))⊗ₜ[ℚ]((1 : S d₂)⊗ₜ[ℚ]v)
    rw [translationS_one]
  exact LinearMap.congr_fun h x

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.CommonTranslation ElementaryPositivity.LaurentAtInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable local instance naturalTaylorTensorRing (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance naturalTaylorTensorAlg (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance naturalTaylorFourRing (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance
noncomputable local instance naturalTaylorFourAlg (d₁ e₁ d₂ e₂ : I → ℕ) :
    Algebra ℚ ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := inferInstance

lemma restrictRows_relativeTaylor {d₁ e₁ d₂ e₂ : I → ℕ}
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) (x : S (d₁+e₁)⊗[ℚ]S (d₂+e₂)) :
    Polynomial.map (restrictRows d₁ e₁ d₂ e₂ A B).toRingHom
      (relativeTaylor (d₁+e₁) (d₂+e₂) x)=
      fourRelativeTaylor d₁ e₁ d₂ e₂ (restrictRows d₁ e₁ d₂ e₂ A B x) := by
  apply polynomial_eq_of_rat_evals
  intro t
  rw [eval_map_rat,relativeTaylor_eval,fourRelativeTaylor_eval]
  have h : (restrictRows d₁ e₁ d₂ e₂ A B).toLinearMap ∘ₗ
      TensorProduct.map (translationS (d₁+e₁) t) LinearMap.id=
      TensorProduct.map (TensorProduct.map (translationS d₁ t) (translationS e₁ t)) LinearMap.id ∘ₗ
        (restrictRows d₁ e₁ d₂ e₂ A B).toLinearMap := by
    apply TensorProduct.ext'
    intro u v
    change restrictTensor A (translationS (d₁+e₁) t u)⊗ₜ[ℚ]restrictTensor B v=
      TensorProduct.map (translationS d₁ t) (translationS e₁ t) (restrictTensor A u)⊗ₜ[ℚ]restrictTensor B v
    rw [restrictTensor_translation]
  exact LinearMap.congr_fun h x

lemma shuffleTensor_translation (a : I → I → ℕ) (d e : I → ℕ) (t : ℚ)
    (x : S d⊗[ℚ]S e) :
    shuffleTensorLinear a d e (TensorProduct.map (translationS d t) (translationS e t) x)=
      translationS (d+e) t (shuffleTensorLinear a d e x) := by
  have h : shuffleTensorLinear a d e ∘ₗ TensorProduct.map (translationS d t) (translationS e t)=
      translationS (d+e) t ∘ₗ shuffleTensorLinear a d e := by
    apply TensorProduct.ext'
    intro u v
    simp only [LinearMap.comp_apply,TensorProduct.map_tmul,shuffleTensorLinear_tmul]
    exact (translation_shufflePolynomial a t u v).symm
  exact LinearMap.congr_fun h x

lemma twoTarget_relativeTaylor (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (x : (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :
    polynomialMapLinear (twoTargetTransfer a d₁ e₁ d₂ e₂) (fourRelativeTaylor d₁ e₁ d₂ e₂ x)=
      relativeTaylor (d₁+e₁) (d₂+e₂) (twoTargetTransfer a d₁ e₁ d₂ e₂ x) := by
  apply polynomial_eq_of_rat_evals
  intro t
  rw [polynomialMapLinear_eval_rat,fourRelativeTaylor_eval,relativeTaylor_eval]
  have h : twoTargetTransfer a d₁ e₁ d₂ e₂ ∘ₗ
      TensorProduct.map (TensorProduct.map (translationS d₁ t) (translationS e₁ t)) LinearMap.id=
      TensorProduct.map (translationS (d₁+e₁) t) LinearMap.id ∘ₗ
        twoTargetTransfer a d₁ e₁ d₂ e₂ := by
    apply TensorProduct.ext'
    intro u v
    change shuffleTensorLinear a d₁ e₁ (TensorProduct.map (translationS d₁ t) (translationS e₁ t) u)⊗ₜ[ℚ]
        shuffleTensorLinear a d₂ e₂ v=
      translationS (d₁+e₁) t (shuffleTensorLinear a d₁ e₁ u)⊗ₜ[ℚ]shuffleTensorLinear a d₂ e₂ v
    rw [shuffleTensor_translation]
  exact LinearMap.congr_fun h x

lemma twoTarget_polynomial_relativeTaylor (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (x : (S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :
    mapLinear (twoTargetTransfer a d₁ e₁ d₂ e₂) (polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂ x))=
      polynomial (relativeTaylor (d₁+e₁) (d₂+e₂) (twoTargetTransfer a d₁ e₁ d₂ e₂ x)) := by
  rw [polynomial_mapLinear,twoTarget_relativeTaylor]

end ElementaryPositivity.RawShuffle

end

end OAI
