import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.UnitalFiltration
import OAI.Combinatorics.Chromatic.Walls.TensorMiddleFiltration

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open HahnSeries SeparationInfinity
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.LinearDetection
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable local instance braidFourTensor (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    CommRing (B a μ d⊗[ℚ]B a μ e) := inferInstance
noncomputable local instance braidFourTensorAlg (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Algebra ℚ (B a μ d⊗[ℚ]B a μ e) := inferInstance
noncomputable local instance braidFourRing (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    CommRing ((B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂)) := inferInstance
noncomputable local instance braidFourAlg (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    Algebra ℚ ((B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂)) := inferInstance

noncomputable local instance braidFourTensorN (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (B a μ d⊗[ℚ]B a μ e) := (braidFourTensor a μ d e).toNonUnitalNonAssocSemiring
noncomputable local instance braidFourTensorM (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Module (B a μ d⊗[ℚ]B a μ e) (B a μ d⊗[ℚ]B a μ e) := Semiring.toModule
noncomputable local instance braidFourN (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    NonUnitalNonAssocSemiring ((B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂)) :=
  (braidFourRing a μ d₁ e₁ d₂ e₂).toNonUnitalNonAssocSemiring
noncomputable local instance braidFourM (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    Module ((B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂))
      ((B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂)) := Semiring.toModule

noncomputable def crossingColumnBAlg (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    B a μ e₁⊗[ℚ]B a μ d₂ →ₐ[ℚ](B a μ d₁⊗[ℚ]B a μ e₁)⊗[ℚ](B a μ d₂⊗[ℚ]B a μ e₂) :=
  middleEmbedding

noncomputable def fourUnitalFiltration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d₁ e₁ d₂ e₂ : I → ℕ) (W : ℤ) :=
  additiveTensorFiltration (unitalSourceTensorFiltration a c η hc θ d₁ e₁)
    (unitalSourceTensorFiltration a c η hc θ d₂ e₂) W

lemma fourBraidingCoefficient_next (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d₁ e₁ d₂ e₂ : I → ℕ) (W : ℤ)
    (x : (B a (slope c η) d₁⊗[ℚ]B a (slope c η) e₁)⊗[ℚ]
      (B a (slope c η) d₂⊗[ℚ]B a (slope c η) e₂))
    (hx : x∈fourUnitalFiltration a c η hc θ d₁ e₁ d₂ e₂ W) (j : ℤ) :
    crossingColumnBAlg a (slope c η) d₁ e₁ d₂ e₂
      (((braidingRatioUnit a (slope c η) e₁ d₂).val-1).coeff j)*x∈
      fourUnitalFiltration a c η hc θ d₁ e₁ d₂ e₂ (W+1) := by
  exact middleAction_mem_filtration (unitalSourceFiltration a c η hc θ d₁)
    (unitalSourceFiltration a c η hc θ d₂) (unitalSourceFiltration a c η hc θ e₁)
    (unitalSourceFiltration a c η hc θ e₂) 1 _
    (fun v w f g hf hg=>braidingDifference_coeff_mul_unital_next a c η hc θ hχ e₁ d₂
      (v+w) (f⊗ₜ[ℚ]g) (tmul_mem_additiveTensorFiltration _ _ (le_refl _) hf hg) j) W x hx

lemma map_sub_one_mul {R T : Type*} [Ring R] [Ring T] (f : R →+* T) (x : R) (y : T) :
    f (x-1)*y=f x*y-y := by rw [map_sub,map_one,sub_mul,one_mul]

lemma fourBraiding_coeff_next (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d₁ e₁ d₂ e₂ : I → ℕ) (W : ℤ)
    (F : LaurentSeries ((B a (slope c η) d₁⊗[ℚ]B a (slope c η) e₁)⊗[ℚ]
      (B a (slope c η) d₂⊗[ℚ]B a (slope c η) e₂)))
    (hF : ∀ j,F.coeff j∈fourUnitalFiltration a c η hc θ d₁ e₁ d₂ e₂ W) (k : ℤ) :
    (mapRing (crossingColumnBAlg a (slope c η) d₁ e₁ d₂ e₂).toRingHom
      (braidingRatioUnit a (slope c η) e₁ d₂).val*F-F).coeff k∈
      fourUnitalFiltration a c η hc θ d₁ e₁ d₂ e₂ (W+1) := by
  classical
  have he : mapRing (crossingColumnBAlg a (slope c η) d₁ e₁ d₂ e₂).toRingHom
      ((braidingRatioUnit a (slope c η) e₁ d₂).val-1)*F=
      mapRing (crossingColumnBAlg a (slope c η) d₁ e₁ d₂ e₂).toRingHom
      (braidingRatioUnit a (slope c η) e₁ d₂).val*F-F := map_sub_one_mul _ _ _
  rw [←he,coeff_mul]
  apply Submodule.sum_mem
  intro ij hij
  exact fourBraidingCoefficient_next a c η hc θ hχ d₁ e₁ d₂ e₂ W _ (hF ij.2) ij.1

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LinearDetection ElementaryPositivity.LaurentAtInfinity
open ElementaryPositivity.SlopeArithmetic
open HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable local instance unitalSepTensor (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    CommRing (B a μ d⊗[ℚ]B a μ e) := inferInstance
noncomputable local instance unitalSepTensorA (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Algebra ℚ (B a μ d⊗[ℚ]B a μ e) := inferInstance

noncomputable local instance unitalSepTensorN (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    NonUnitalNonAssocSemiring (B a μ d⊗[ℚ]B a μ e) := (unitalSepTensor a μ d e).toNonUnitalNonAssocSemiring
noncomputable local instance unitalSepTensorM (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Module (B a μ d⊗[ℚ]B a μ e) (B a μ d⊗[ℚ]B a μ e) := Semiring.toModule

lemma unitalSourceFiltration_translation_mem (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d : I → ℕ) (W : ℤ) (f : B a (slope c η) d)
    (hf : f∈unitalSourceFiltration a c η hc θ d W) (t : ℚ) :
    translationB a (slope c η) d t f∈unitalSourceFiltration a c η hc θ d W := by
  classical
  by_cases hd : d=0
  · by_cases hw : W≤0
    · simp only [unitalSourceFiltration,ite_eq_left hd,ite_eq_left hw,Submodule.mem_top]
    · simp only [unitalSourceFiltration,ite_eq_left hd,ite_eq_right hw,Submodule.mem_bot] at hf ⊢
      rw [hf,map_zero]
  · rw [unitalSourceFiltration_nonzero a c η hc θ d hd W] at hf ⊢
    exact sourceFiltration_translation_mem a c η hc θ d W f hf t

lemma unitalSourceTensorFiltration_translateLeft (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) (t : ℚ)
    (x : B a (slope c η) d ⊗[ℚ] B a (slope c η) e)
    (hx : x∈unitalSourceTensorFiltration a c η hc θ d e W) :
    TensorProduct.map (translationB a (slope c η) d t)
      (LinearMap.id : B a (slope c η) e →ₗ[ℚ] B a (slope c η) e) x ∈
      unitalSourceTensorFiltration a c η hc θ d e W := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u,v,f,g,hw,hf,hg,rfl⟩:=hx
    rw [TensorProduct.map_tmul,LinearMap.id_apply]
    exact tmul_mem_additiveTensorFiltration _ _ hw
      (unitalSourceFiltration_translation_mem a c η hc θ d u f hf t) hg
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul q x _ hx => rw [map_smul]; exact Submodule.smul_mem _ q hx

noncomputable def unitalRestrictionRelativeB (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) :
    B a (slope c η) (d+e) →ₐ[ℚ] Polynomial (B a (slope c η) d ⊗[ℚ] B a (slope c η) e) :=
  (relativeTaylorB a (slope c η) d e).comp (restrictionBUnit a c η hc hs (firstCut d e))

lemma unitalRestrictionRelativeB_coeff_filtration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e)
    (W : ℤ) (f : B a (slope c η) (d+e))
    (hf : f∈unitalSourceFiltration a c η hc θ (d+e) W) (n : ℕ) :
    (unitalRestrictionRelativeB a c η hc hs f).coeff n∈unitalSourceTensorFiltration a c η hc θ d e W := by
  apply ElementaryPositivity.CommonTranslation.polynomial_coeff_mem
  intro t
  change (relativeTaylorB a (slope c η) d e
    (restrictionBUnit a c η hc hs (firstCut d e) f)).eval _ ∈ _
  rw [relativeTaylorB_eval]
  exact unitalSourceTensorFiltration_translateLeft a c η hc θ d e W t _
    (restrictionBUnit_unitalSourceTensorFiltration a c η hc θ d e hs (firstCut d e) W f hf)

noncomputable def unitalSourceTensorFiltrationIdeal (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) : Ideal (B a (slope c η) d⊗[ℚ]B a (slope c η) e) :=
  additiveTensorFiltrationIdeal (unitalSourceFiltration a c η hc θ d) (unitalSourceFiltration a c η hc θ e)
    (unitalSourceFiltration_mul_mem a c η hc θ d) (unitalSourceFiltration_mul_mem a c η hc θ e) W

namespace SeparationInfinity
noncomputable def unitalSeparationSeries (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e) :
    B a (slope c η) (d+e) →ₗ[ℚ] LaurentSeries (B a (slope c η) d⊗[ℚ]B a (slope c η) e) :=
  (mulPolynomial (quotientInverseKernelUnit a (slope c η) d e).val).comp
    (unitalRestrictionRelativeB a c η hc hs).toLinearMap

lemma unitalSeparationSeries_coeff_filtration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e)
    (W j : ℤ) (f : B a (slope c η) (d+e))
    (hf : f∈unitalSourceFiltration a c η hc θ (d+e) W) :
    (unitalSeparationSeries a c η hc hs f).coeff j∈unitalSourceTensorFiltration a c η hc θ d e W := by
  have H := mulPolynomialCoeff_mem (unitalSourceTensorFiltrationIdeal a c η hc θ d e W)
    (quotientInverseKernelUnit a (slope c η) d e).val (-j)
    (unitalRestrictionRelativeB a c η hc hs f)
    (unitalRestrictionRelativeB_coeff_filtration a c η hc θ d e hs W f hf)
  change mulPolynomialCoeff (quotientInverseKernelUnit a (slope c η) d e).val (-j)
    (unitalRestrictionRelativeB a c η hc hs f)∈unitalSourceTensorFiltration a c η hc θ d e W at H
  simpa only [mulPolynomialCoeff_apply,neg_neg,unitalSeparationSeries,LinearMap.comp_apply,
    mulPolynomial_apply,AlgHom.toLinearMap_apply] using H

lemma quotientInverseKernelUnit_zero_left (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (e : I → ℕ) :
    quotientInverseKernelUnit a μ 0 e=1 := by
  simp only [quotientInverseKernelUnit,inverseKernelUnit_zero_left,map_one]
lemma quotientInverseKernelUnit_zero_right (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    quotientInverseKernelUnit a μ d 0=1 := by
  simp only [quotientInverseKernelUnit,inverseKernelUnit_zero_right,map_one]

lemma unitalSeparationSeries_coeff_positive_next (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (d e : I → ℕ)
    (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e)
    (W j : ℤ) (hj : 0<j) (f : B a (slope c η) (d+e))
    (hf : f∈unitalSourceFiltration a c η hc θ (d+e) W) :
    (unitalSeparationSeries a c η hc hs f).coeff j∈unitalSourceTensorFiltration a c η hc θ d e (W+1) := by
  by_cases hd : d=0
  · subst d
    change ((quotientInverseKernelUnit a (slope c η) 0 e).val*
      polynomial (unitalRestrictionRelativeB a c η hc hs f)).coeff j∈unitalSourceTensorFiltration a c η hc θ 0 e (W+1)
    rw [quotientInverseKernelUnit_zero_left,Units.val_one,one_mul,polynomial_coeff_positive _ j hj]
    exact Submodule.zero_mem _
  by_cases he : e=0
  · subst e
    change ((quotientInverseKernelUnit a (slope c η) d 0).val*
      polynomial (unitalRestrictionRelativeB a c η hc hs f)).coeff j∈unitalSourceTensorFiltration a c η hc θ d 0 (W+1)
    rw [quotientInverseKernelUnit_zero_right,Units.val_one,one_mul,polynomial_coeff_positive _ j hj]
    exact Submodule.zero_mem _
  have hde : d+e≠0 := add_ne_zero_left _ _ hd
  have hs' := hs.resolve_left hd |>.resolve_left he
  rw [unitalSourceFiltration_nonzero a c η hc θ (d+e) hde W] at hf
  rw [unitalSourceTensorFiltration_nonzero a c η hc θ d e hd he]
  have hn := separationCoefficient_negative_filtration a c η hc θ hχ d e hs' W (-j) (by omega) f hf
  have heq : unitalRestrictionRelativeB a c η hc hs=restrictionRelativeB a c η hc hs' (firstCut d e) := by
    unfold unitalRestrictionRelativeB restrictionRelativeB
    congr 1
  simp only [unitalSeparationSeries,LinearMap.comp_apply,heq]
  simpa only [separationCoefficient_eq_coeff,neg_neg,separationSeries,LinearMap.comp_apply] using hn
end SeparationInfinity
end ElementaryPositivity.RawShuffle

end

end OAI
