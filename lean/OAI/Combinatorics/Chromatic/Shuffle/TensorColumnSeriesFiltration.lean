import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.FourBraiding
import OAI.Combinatorics.Chromatic.Shuffle.GridQuotient
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentConstantMultiplication

namespace OAI

section
namespace ElementaryPositivity.TensorColumns
open scoped TensorProduct
open ElementaryPositivity.LinearDetection ElementaryPositivity.LaurentAtInfinity
open HahnSeries
variable {A B C D : Type*}
  [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra ℚ A] [Algebra ℚ B] [Algebra ℚ C] [Algebra ℚ D]

noncomputable def seriesProduct (f : LaurentSeries (A⊗[ℚ]B)) (g : LaurentSeries (C⊗[ℚ]D)) :
    LaurentSeries ((A⊗[ℚ]C)⊗[ℚ](B⊗[ℚ]D)) :=
  mapRing (first (K:=ℚ) (A:=A) (B:=B) (C:=C) (D:=D)).toRingHom f *
    mapRing (second (K:=ℚ) (A:=A) (B:=B) (C:=C) (D:=D)).toRingHom g

lemma seriesProduct_coeff_filtration
    (P : ℤ → Submodule ℚ A) (Q : ℤ → Submodule ℚ B)
    (R : ℤ → Submodule ℚ C) (S : ℤ → Submodule ℚ D)
    (U V : ℤ) (f : LaurentSeries (A⊗[ℚ]B)) (g : LaurentSeries (C⊗[ℚ]D))
    (hf : ∀ j,f.coeff j∈additiveTensorFiltration P Q U)
    (hg : ∀ j,g.coeff j∈additiveTensorFiltration R S V) (k : ℤ) :
    (seriesProduct f g).coeff k∈
      additiveTensorFiltration (additiveTensorFiltration P R) (additiveTensorFiltration Q S) (U+V) := by
  classical
  rw [seriesProduct,coeff_mul]
  apply Submodule.sum_mem
  intro ij hij
  change first (f.coeff ij.1)*second (g.coeff ij.2)∈
    additiveTensorFiltration (additiveTensorFiltration P R) (additiveTensorFiltration Q S) (U+V)
  rw [product]
  exact interchange_mem_filtration P Q R S U V _ _ (hf _) (hg _)

lemma seriesProduct_constant_filtration
    (P : ℤ → Submodule ℚ A) (Q : ℤ → Submodule ℚ B)
    (R : ℤ → Submodule ℚ C) (S : ℤ → Submodule ℚ D)
    (U V : ℤ) (f : LaurentSeries (A⊗[ℚ]B)) (g : LaurentSeries (C⊗[ℚ]D))
    (hf : ∀ j,f.coeff j∈additiveTensorFiltration P Q U)
    (hg : ∀ j,g.coeff j∈additiveTensorFiltration R S V)
    (hf' : ∀ j,0<j → f.coeff j∈additiveTensorFiltration P Q (U+1))
    (hg' : ∀ j,0<j → g.coeff j∈additiveTensorFiltration R S (V+1)) :
    (seriesProduct f g).coeff 0-
      TensorProduct.tensorTensorTensorComm ℚ A B C D (f.coeff 0⊗ₜ[ℚ]g.coeff 0)∈
      additiveTensorFiltration (additiveTensorFiltration P R) (additiveTensorFiltration Q S) (U+V+1) := by
  rw [←product]
  unfold seriesProduct
  apply coeff_mul_zero_sub_mem_of_positive
  intro i j hij
  change first (f.coeff i)*second (g.coeff j)∈
    additiveTensorFiltration (additiveTensorFiltration P R) (additiveTensorFiltration Q S) (U+V+1)
  rw [product]
  rcases hij with hi|hj
  · convert interchange_mem_filtration P Q R S (U+1) V _ _ (hf' i hi) (hg j) using 1
    congr 1
    omega
  · convert interchange_mem_filtration P Q R S U (V+1) _ _ (hf i) (hg' j hj) using 1
    congr 1
    omega

end ElementaryPositivity.TensorColumns

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.LinearDetection
open ElementaryPositivity.SlopeArithmetic
open HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] braidFourTensor braidFourTensorAlg braidFourRing braidFourAlg
attribute [local instance] braidFourTensorN braidFourTensorM braidFourN braidFourM

noncomputable def fourInputSeriesB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (hd : d₁=0 ∨ d₂=0 ∨ slope c η d₁=slope c η d₂)
    (he : e₁=0 ∨ e₂=0 ∨ slope c η e₁=slope c η e₂)
    (f : B a (slope c η) (d₁+d₂)) (g : B a (slope c η) (e₁+e₂)) :
    LaurentSeries ((B a (slope c η) d₁⊗[ℚ]B a (slope c η) e₁)⊗[ℚ]
      (B a (slope c η) d₂⊗[ℚ]B a (slope c η) e₂)) :=
  mapRing (crossingColumnBAlg a (slope c η) d₁ e₁ d₂ e₂).toRingHom
    (braidingRatioUnit a (slope c η) e₁ d₂).val *
  ElementaryPositivity.TensorColumns.seriesProduct
    (unitalSeparationSeries a c η hc hd f) (unitalSeparationSeries a c η hc he g)

lemma fourInputSeriesB_constant_next (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (hd : d₁=0 ∨ d₂=0 ∨ slope c η d₁=slope c η d₂)
    (he : e₁=0 ∨ e₂=0 ∨ slope c η e₁=slope c η e₂)
    (U V : ℤ) (f : B a (slope c η) (d₁+d₂)) (g : B a (slope c η) (e₁+e₂))
    (hf : f∈unitalSourceFiltration a c η hc θ (d₁+d₂) U)
    (hg : g∈unitalSourceFiltration a c η hc θ (e₁+e₂) V) :
    (fourInputSeriesB a c η hc d₁ e₁ d₂ e₂ hd he f g).coeff 0-
      fourInterchangeB a (slope c η) d₁ e₁ d₂ e₂
        ((unitalSeparationSeries a c η hc hd f).coeff 0⊗ₜ[ℚ]
          (unitalSeparationSeries a c η hc he g).coeff 0)∈
      fourUnitalFiltration a c η hc θ d₁ e₁ d₂ e₂ (U+V+1) := by
  let P:=unitalSourceFiltration a c η hc θ
  let F:=unitalSeparationSeries a c η hc hd f
  let G:=unitalSeparationSeries a c η hc he g
  let H:=ElementaryPositivity.TensorColumns.seriesProduct F G
  have hF (j) := unitalSeparationSeries_coeff_filtration a c η hc θ d₁ d₂ hd U j f hf
  have hG (j) := unitalSeparationSeries_coeff_filtration a c η hc θ e₁ e₂ he V j g hg
  have hH (j) : H.coeff j∈fourUnitalFiltration a c η hc θ d₁ e₁ d₂ e₂ (U+V) :=
    ElementaryPositivity.TensorColumns.seriesProduct_coeff_filtration
      (P d₁) (P d₂) (P e₁) (P e₂) U V F G hF hG j
  have h₁ := fourBraiding_coeff_next a c η hc θ hχ d₁ e₁ d₂ e₂ (U+V) H hH 0
  have h₂ := ElementaryPositivity.TensorColumns.seriesProduct_constant_filtration
    (P d₁) (P d₂) (P e₁) (P e₂) U V F G hF hG
    (fun j hj=>unitalSeparationSeries_coeff_positive_next a c η hc θ hχ d₁ d₂ hd U j hj f hf)
    (fun j hj=>unitalSeparationSeries_coeff_positive_next a c η hc θ hχ e₁ e₂ he V j hj g hg)
  rw [coeff_sub] at h₁
  have h:=Submodule.add_mem (fourUnitalFiltration a c η hc θ d₁ e₁ d₂ e₂ (U+V+1)) h₁ h₂
  simpa only [fourInputSeriesB,fourInterchangeB,F,G,H,sub_add_sub_cancel] using h

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle.SeparationInfinity
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable local instance unitalNatS (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance unitalNatSA (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance unitalNatB (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    CommRing (B a μ d⊗[ℚ]B a μ e) := inferInstance
noncomputable local instance unitalNatBA (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Algebra ℚ (B a μ d⊗[ℚ]B a μ e) := inferInstance

lemma unitalRestrictionRelativeB_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (f : S (d+e)) :
    unitalRestrictionRelativeB a c η hc hs (quotientAlg a (slope c η) (d+e) f)=
    Polynomial.map (quotientTensor a (slope c η) d e).toRingHom
      (relativeTaylor d e (restrictTensor (firstCut d e) f)) := by
  rw [relativeTaylor_quotient]
  rfl

lemma unitalSeparationSeries_mk (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) (f : S (d+e)) :
    unitalSeparationSeries a c η hc hs (quotientAlg a (slope c η) (d+e) f)=
    mapRing (quotientTensor a (slope c η) d e).toRingHom (tensorSeparationSeries a d e f) := by
  rw [tensorSeparationSeries,mapRing_mul_polynomial]
  dsimp only [unitalSeparationSeries,LinearMap.comp_apply,AlgHom.toLinearMap_apply]
  rw [unitalRestrictionRelativeB_mk]
  rfl

end ElementaryPositivity.RawShuffle.SeparationInfinity

end

end OAI
