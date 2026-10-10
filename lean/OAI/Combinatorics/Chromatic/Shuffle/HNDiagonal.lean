import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.UnitalFiltration

namespace OAI

namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity SeparationInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] cancelTensorRing cancelTensorAlg cancelFourRing cancelFourAlg
attribute [local instance] cancelTensorDistrib cancelTensorSelf cancelTensorNonUnital cancelFourNonUnital cancelSeriesRing
attribute [local instance] cellSepTensorSemiring cellSepTensorNonAssoc cellSepFourSemiring cellSepFourNonAssoc cellSepFourModule

lemma mappedInverseKernel_zero_head {R : Type*} [CommRing R] [Algebra ℚ R]
    (a : I → I → ℕ) (e : I → ℕ) (F : S 0⊗[ℚ]S e →ₐ[ℚ]R) :
    mappedInverseKernel a 0 e F=1 := by
  unfold mappedInverseKernel
  rw [inverseKernelUnit_zero_left,map_one]

lemma mappedInverseRatio_zero_head {R : Type*} [CommRing R] [Algebra ℚ R]
    (a b : I → I → ℕ) (e : I → ℕ) (F : S 0⊗[ℚ]S e →ₐ[ℚ]R) :
    (mappedInverseKernel a 0 e F*(mappedInverseKernel b 0 e F)⁻¹).val=1 := by
  rw [mappedInverseKernel_zero_head,mappedInverseKernel_zero_head,inv_one,mul_one,Units.val_one]

lemma separation_zero_right (a : I → I → ℕ) (d : I → ℕ) (f : S d) :
    tensorSeparationSeries a d 0 (castS (add_zero d).symm f)=
    polynomial (relativeTaylor d 0 (f⊗ₜ[ℚ](1 : S 0))) := by
  rw [tensorSeparationSeries,inverseKernelUnit_zero_right,Units.val_one,one_mul,restrictTensor_zero_right]
lemma separation_zero_left (a : I → I → ℕ) (e : I → ℕ) (g : S e) :
    tensorSeparationSeries a 0 e (castS (zero_add e).symm g)=
    polynomial (relativeTaylor 0 e ((1 : S 0)⊗ₜ[ℚ]g)) := by
  rw [tensorSeparationSeries,inverseKernelUnit_zero_left,Units.val_one,one_mul,restrictTensor_zero_left]

lemma polynomial_mapped_product_two {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* T) (g : S →+* T) (p : Polynomial R) (q : Polynomial S) :
    polynomial (Polynomial.map f p * Polynomial.map g q)=
      mapRing f (polynomial p)*mapRing g (polynomial q) := by
  rw [polynomial.map_mul,←polynomial_map,←polynomial_map]

omit [Fintype I] [DecidableEq I] in
lemma fourPolynomial_mapped_product_two (d₁ e₁ d₂ e₂ : I → ℕ)
    (p : Polynomial (S d₁⊗[ℚ]S d₂)) (q : Polynomial (S e₁⊗[ℚ]S e₂)) :
    polynomial (Polynomial.map (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom p *
      Polynomial.map (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom q)=
      mapRing (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom (polynomial p)*
        mapRing (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom (polynomial q) :=
  @polynomial_mapped_product_two (S d₁⊗[ℚ]S d₂) (S e₁⊗[ℚ]S e₂)
    ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂))
    (cancelTensorRing d₁ d₂) (cancelTensorRing e₁ e₂) (cancelFourRing d₁ e₁ d₂ e₂)
    (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom p q

lemma fourTaylor_column_product (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S d₁⊗[ℚ]S d₂) (g : S e₁⊗[ℚ]S e₂) :
    mapRing (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom (polynomial (relativeTaylor d₁ d₂ f)) *
      mapRing (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom (polynomial (relativeTaylor e₁ e₂ g))=
    polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂ (fourInterchange d₁ e₁ d₂ e₂ (f⊗ₜ[ℚ]g))) := by
  rw [←fourPolynomial_mapped_product_two]
  apply congrArg polynomial
  rw [firstColumn_relativeTaylor, secondColumn_relativeTaylor]
  exact ((fourRelativeTaylor d₁ e₁ d₂ e₂).map_mul
    (firstColumnAlg d₁ e₁ d₂ e₂ f) (secondColumnAlg d₁ e₁ d₂ e₂ g)).symm.trans
    (congrArg (fourRelativeTaylor d₁ e₁ d₂ e₂)
      (fourColumns_product d₁ e₁ d₂ e₂ f g))

lemma fourInputSeries_head (a : I → I → ℕ) (d e : I → ℕ) (f : S d) (g : S e) :
    fourInputSeries a d 0 0 e (castS (add_zero d).symm f) (castS (zero_add e).symm g)=
    polynomial (fourRelativeTaylor d 0 0 e ((f⊗ₜ[ℚ](1 : S 0))⊗ₜ[ℚ]((1 : S 0)⊗ₜ[ℚ]g))) := by
  unfold fourInputSeries
  have hf := congrArg (mapRing (firstColumnAlg d 0 0 e).toRingHom)
    (separation_zero_right a d f)
  have hg := congrArg (mapRing (secondColumnAlg d 0 0 e).toRingHom)
    (separation_zero_left a e g)
  have hkernel := mappedInverseRatio_zero_head a (fun i j => a j i)
    (0 : I → ℕ) (crossingColumnAlg d 0 0 e)
  exact (congrArg₂ (· * ·) (congrArg₂ (· * ·) hf hg) hkernel).trans
    ((mul_one _).trans (fourTaylor_column_product d 0 0 e _ _))

noncomputable def rawClearedSeparation (a : I → I → ℕ) (d e : I → ℕ) :
    S d⊗[ℚ]S e →ₗ[ℚ] LaurentSeries (S d⊗[ℚ]S e) :=
  (mulPolynomial (inverseKernelUnit a d e*(inverseKernelUnit (fun _ _ : I=>0) d e)⁻¹).val).comp
    (relativeTaylor d e).toLinearMap

noncomputable def rawRelativeSeries (d e : I → ℕ) (x : S d⊗[ℚ]S e) :
    LaurentSeries (S d⊗[ℚ]S e) := polynomial (relativeTaylor d e x)

lemma cellTransfer_head_normalized (a : I → I → ℕ) (d e : I → ℕ) (f : S d) (g : S e) :
    rawClearedSeparation a (d+0) (0+e)
        (cellTransfer a d 0 0 e
          (fourGridPolynomial a (castS (add_zero d).symm f) (castS (zero_add e).symm g) d 0 0 e))=
    rawRelativeSeries (d+0) (0+e)
      (castS (add_zero d).symm f⊗ₜ[ℚ]castS (zero_add e).symm g) := by
  unfold rawClearedSeparation
  simp only [LinearMap.comp_apply,mulPolynomial_apply,AlgHom.toLinearMap_apply]
  rw [cellTransfer_normalized,fourInputSeries_head,twoTarget_polynomial_relativeTaylor,
    twoTargetTransfer_tmul,shufflePolynomial_unit_right,shufflePolynomial_unit_left]
  simp [eulerForm,rawRelativeSeries]
end ElementaryPositivity.RawShuffle

end OAI
