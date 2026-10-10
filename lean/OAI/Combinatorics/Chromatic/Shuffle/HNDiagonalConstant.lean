import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.HNDiagonal
import OAI.Combinatorics.Chromatic.Shuffle.CellLeadingSum

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity SeparationInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] clearedSepTensorRing clearedSepTensorAlg clearBTensorB clearBTensorBA

omit [Fintype I] [DecidableEq I] in
lemma rawRelativeSeries_constant (d e : I → ℕ) (x : S d⊗[ℚ]S e) :
    (rawRelativeSeries d e x).coeff 0=x := by
  have ht : translationS d 0=LinearMap.id := by apply LinearMap.ext; intro f; exact translationS_zero d f
  have he := relativeTaylor_eval d e x 0
  rw [map_zero,←Polynomial.coeff_zero_eq_eval_zero,ht,TensorProduct.map_id] at he
  simpa only [rawRelativeSeries,show (0 : ℤ)=-(0 : ℕ) by rfl,polynomial_coeff,LinearMap.id_apply] using he

lemma fourGridPolynomial_castSources (a : I → I → ℕ)
    {d e d' e' : I → ℕ} (h : d=d') (k : e=e') (f : S d) (g : S e)
    (d₁ e₁ d₂ e₂ : I → ℕ) :
    fourGridPolynomial a (castS h f) (castS k g) d₁ e₁ d₂ e₂=
      fourGridPolynomial a f g d₁ e₁ d₂ e₂ := by
  subst d'; subst e'; rfl

lemma clearedConstantB_cell_head (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d e : I → ℕ) (f : S d) (g : S e) :
    clearedConstantB a μ (d+0) (0+e)
      (quotientTensor a μ (d+0) (0+e)
        (cellTransfer a d 0 0 e (fourGridPolynomial a f g d 0 0 e)))=
    quotientTensor a μ (d+0) (0+e)
      (castS (add_zero d).symm f⊗ₜ[ℚ]castS (zero_add e).symm g) := by
  have h := cellTransfer_head_normalized a d e f g
  rw [fourGridPolynomial_castSources] at h
  rw [clearedConstantB_apply,clearedSeparationB_mk]
  change (mapRing (quotientTensor a μ (d+0) (0+e)).toRingHom
    (rawClearedSeparation a (d+0) (0+e) _)).coeff 0=_
  rw [h,mapRing_coeff,rawRelativeSeries_constant]
  rfl

lemma castBTensor_quotient_tmul (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e d' e' : I → ℕ} (h : d=d') (k : e=e') (f : S d) (g : S e) :
    castBTensor a μ h k (quotientTensor a μ d e (f⊗ₜ[ℚ]g))=
      quotientTensor a μ d' e' (castS h f⊗ₜ[ℚ]castS k g) := by
  subst d'; subst e'; rfl

lemma clearedConstantB_cell_head_cast (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d e d₁ e₁ d₂ e₂ : I → ℕ) (h₁ : d₁+e₁=d) (h₂ : d₂+e₂=e)
    (he : e₁=0) (hd : d₂=0) (f : S d) (g : S e) :
    clearedConstantB a μ d e (quotientTensor a μ d e
      (castTensor h₁ h₂ (cellTransfer a d₁ e₁ d₂ e₂
        (fourGridPolynomial a f g d₁ e₁ d₂ e₂))))=
    quotientTensor a μ d e (f⊗ₜ[ℚ]g) := by
  subst e₁; subst d₂
  have h₁' : d₁=d := by simpa only [add_zero] using h₁
  have h₂' : e₂=e := by simpa only [zero_add] using h₂
  subst d₁; subst e₂
  rw [clearedConstantB_castTensor,clearedConstantB_cell_head,castBTensor_quotient_tmul]
  simp only [castS_trans,castS_rfl]
end ElementaryPositivity.RawShuffle

end

end OAI
