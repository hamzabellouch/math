import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.TensorColumnSeriesFiltration
import OAI.Combinatorics.Chromatic.GradedAlgebra.ClearedSeparation

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SlopeArithmetic
open SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable local instance clearBTensorS (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance clearBTensorSA (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance clearBTensorB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    CommRing (B a μ d⊗[ℚ]B a μ e) := inferInstance
noncomputable local instance clearBTensorBA (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Algebra ℚ (B a μ d⊗[ℚ]B a μ e) := inferInstance

noncomputable def clearedSeparationB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    B a μ d⊗[ℚ]B a μ e →ₗ[ℚ] LaurentSeries (B a μ d⊗[ℚ]B a μ e) :=
  (mulPolynomial (mixedInverseKernelUnit a a μ d e *
    (mixedInverseKernelUnit a (fun _ _ : I=>0) μ d e)⁻¹).val).comp
      (relativeTaylorB a μ d e).toLinearMap

lemma mapRing_ratio_val {R T : Type*} [CommRing R] [CommRing T]
    (f : R →+* T) (u v : (LaurentSeries R)ˣ) :
    mapRing f (u*v⁻¹).val=
      (Units.map (mapRing f).toMonoidHom u*(Units.map (mapRing f).toMonoidHom v)⁻¹).val := by
  rw [Units.val_mul,map_mul]
  rfl

lemma clearedSeparationB_mk (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (x : S d⊗[ℚ]S e) :
    clearedSeparationB a μ d e (quotientTensor a μ d e x)=
    mapRing (quotientTensor a μ d e).toRingHom
      ((inverseKernelUnit a d e*(inverseKernelUnit (fun _ _ : I=>0) d e)⁻¹).val *
        polynomial (relativeTaylor d e x)) := by
  rw [mapRing_mul_polynomial,mapRing_ratio_val,relativeTaylor_quotient]
  rfl

variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
lemma unitalSeparationSeries_shuffle_grid (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e α β : I → ℕ} (h : d+e=α+β)
    (hs : α=0 ∨ β=0 ∨ slope c η α=slope c η β)
    (f : S d) (g : S e) {s : ElementaryPositivity.PackConvolution.Pack (A:=A)}
    (R : Realization (α+β) s) :
    unitalSeparationSeries a c η hc hs
      (quotientAlg a (slope c η) (α+β) (castS h (shufflePolynomial a f g)))=
    clearedSeparationB a (slope c η) α β
      (quotientTensor a (slope c η) α β
        (gridTensor a f g (cutRealizationEquiv R (firstCut α β)).val
          (leftRealization R (firstCut α β)) (rightRealization R (firstCut α β)))) := by
  rw [unitalSeparationSeries_mk,separation_shuffle_grid a h f g R,clearedSeparationB_mk]

lemma clearedSeparationB_zero_of_quotient (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ)
    (x : S d⊗[ℚ]S e) (hx : quotientTensor a μ d e x=0) :
    clearedSeparationB a μ d e (quotientTensor a μ d e x)=0 := by
  rw [hx]
  exact (clearedSeparationB a μ d e).map_zero

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.LinearDetection
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable local instance gridTensorBCommRing (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    CommRing (B a μ d ⊗[ℚ] B a μ e) := inferInstance
noncomputable local instance gridTensorBAlgebra (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Algebra ℚ (B a μ d ⊗[ℚ] B a μ e) := inferInstance

lemma quotient_cellTransfer_filtered (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (hd : d₁=0 ∨ d₂=0 ∨ slope c η d₁=slope c η d₂)
    (he : e₁=0 ∨ e₂=0 ∨ slope c η e₁=slope c η e₂)
    (h₁ : d₁=0 ∨ e₁=0 ∨ slope c η d₁=slope c η e₁)
    (h₂ : d₂=0 ∨ e₂=0 ∨ slope c η d₂=slope c η e₂)
    (ih₁ : ∀ u v x y,x∈unitalSourceFiltration a c η hc θ d₁ u →
      y∈unitalSourceFiltration a c η hc θ e₁ v →
      shuffleBUnit a c η hc d₁ e₁ h₁ x y∈unitalSourceFiltration a c η hc θ (d₁+e₁) (u+v))
    (ih₂ : ∀ u v x y,x∈unitalSourceFiltration a c η hc θ d₂ u →
      y∈unitalSourceFiltration a c η hc θ e₂ v →
      shuffleBUnit a c η hc d₂ e₂ h₂ x y∈unitalSourceFiltration a c η hc θ (d₂+e₂) (u+v))
    (U V : ℤ) (f : S (d₁+d₂)) (g : S (e₁+e₂))
    (hf : quotientAlg a (slope c η) (d₁+d₂) f∈unitalSourceFiltration a c η hc θ (d₁+d₂) U)
    (hg : quotientAlg a (slope c η) (e₁+e₂) g∈unitalSourceFiltration a c η hc θ (e₁+e₂) V) :
    quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂)
      (cellTransfer a d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂))∈
    unitalSourceTensorFiltration a c η hc θ (d₁+e₁) (d₂+e₂) (U+V) := by
  let F := unitalSourceFiltration a c η hc θ
  have hm (d) := unitalSourceFiltration_mul_mem a c η hc θ d
  have htf := restrictionBUnit_unitalSourceTensorFiltration a c η hc θ d₁ d₂ hd
    (firstCut d₁ d₂) U _ hf
  have htg := restrictionBUnit_unitalSourceTensorFiltration a c η hc θ e₁ e₂ he
    (firstCut e₁ e₂) V _ hg
  have hx := interchange_mem_filtration (F d₁) (F d₂) (F e₁) (F e₂) U V _ _ htf htg
  have hmul := additiveTensorFiltration_mul_mem
    (additiveTensorFiltration (F d₁) (F e₁)) (additiveTensorFiltration (F d₂) (F e₂))
    (additiveTensorFiltration_mul_mem (F d₁) (F e₁) (hm d₁) (hm e₁))
    (additiveTensorFiltration_mul_mem (F d₂) (F e₂) (hm d₂) (hm e₂)) (U+V) _
    (fourQuotient a (slope c η) d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂)) hx
  erw [←fourQuotient_grid_factor a c η hc d₁ e₁ d₂ e₂ hd he
    (firstCut d₁ d₂) (firstCut e₁ e₂) f g] at hmul
  change quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂)
    (twoTargetTransfer a d₁ e₁ d₂ e₂ _)∈_
  rw [quotient_twoTargetTransfer_unit a c η hc d₁ e₁ d₂ e₂ h₁ h₂]
  exact tensor_map_mem_filtration _ _ (F (d₁+e₁)) (F (d₂+e₂))
    (shuffleTensorBUnit a c η hc d₁ e₁ h₁) (shuffleTensorBUnit a c η hc d₂ e₂ h₂)
    (lift_mem_filtration _ _ _ (unitalSourceFiltration_antitone a c η hc θ (d₁+e₁)) _ ih₁)
    (lift_mem_filtration _ _ _ (unitalSourceFiltration_antitone a c η hc θ (d₂+e₂)) _ ih₂)
    (U+V) _ hmul

end ElementaryPositivity.RawShuffle

end

end OAI
