import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.TensorFiltration
import OAI.Combinatorics.Chromatic.Shuffle.CrossScalar
import OAI.Combinatorics.Chromatic.Walls.TensorFiltrationIdeals
import OAI.Combinatorics.Chromatic.Walls.LaurentPolynomialAction

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
namespace SeparationInfinity

noncomputable def separationSeries (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) :
    B a (SlopeArithmetic.slope c η) (d+e) →ₗ[ℚ]
      LaurentSeries (B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e) :=
  (mulPolynomial (quotientInverseKernelUnit a (SlopeArithmetic.slope c η) d e).val).comp
    (restrictionRelativeB a c η hc hs (firstCut d e)).toLinearMap

noncomputable def separationCoefficient (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (j : ℤ) :
    B a (SlopeArithmetic.slope c η) (d+e) →ₗ[ℚ]
      B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e :=
  (mulPolynomialCoeff (quotientInverseKernelUnit a (SlopeArithmetic.slope c η) d e).val j).comp
    (restrictionRelativeB a c η hc hs (firstCut d e)).toLinearMap

@[simp] lemma separationCoefficient_apply (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (j : ℤ)
    (f : B a (SlopeArithmetic.slope c η) (d+e)) :
    separationCoefficient a c η hc hs j f =
      mulPolynomialCoeff (quotientInverseKernelUnit a (SlopeArithmetic.slope c η) d e).val j
        (restrictionRelativeB a c η hc hs (firstCut d e) f) := rfl

lemma separationCoefficient_eq_coeff (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    {d e : I → ℕ} (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e) (j : ℤ)
    (f : B a (SlopeArithmetic.slope c η) (d+e)) :
    separationCoefficient a c η hc hs j f = (separationSeries a c η hc hs f).coeff (-j) := rfl

end SeparationInfinity
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LinearDetection
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

lemma sourceTensorFiltration_translateLeft (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) (t : ℚ)
    (x : B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e)
    (hx : x∈sourceTensorFiltration a c η hc θ d e W) :
    TensorProduct.map (translationB a (SlopeArithmetic.slope c η) d t)
      (LinearMap.id : B a (SlopeArithmetic.slope c η) e →ₗ[ℚ] B a (SlopeArithmetic.slope c η) e) x ∈
      sourceTensorFiltration a c η hc θ d e W := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u,v,f,g,hw,hf,hg,rfl⟩:=hx
    rw [TensorProduct.map_tmul,LinearMap.id_apply]
    exact tmul_mem_additiveTensorFiltration _ _ hw
      (sourceFiltration_translation_mem a c η hc θ d u f hf t) hg
  | zero => rw [map_zero]; exact (sourceTensorFiltration a c η hc θ d e W).zero_mem
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (sourceTensorFiltration a c η hc θ d e W).add_mem hx hy
  | smul q x _ hx =>
    rw [map_smul]
    exact (sourceTensorFiltration a c η hc θ d e W).smul_mem q hx

lemma restrictionRelativeB_coeff_filtration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (W : ℤ) (f : B a (SlopeArithmetic.slope c η) (d+e))
    (hf : f∈sourceFiltration a c η hc θ (d+e) W) (n : ℕ) :
    (restrictionRelativeB a c η hc hs (firstCut d e) f).coeff n∈
      sourceTensorFiltration a c η hc θ d e W := by
  apply ElementaryPositivity.CommonTranslation.polynomial_coeff_mem
  intro t
  change (relativeTaylorB a (SlopeArithmetic.slope c η) d e
    (restrictionB a c η hc hs (firstCut d e) f)).eval _ ∈ _
  rw [relativeTaylorB_eval]
  exact sourceTensorFiltration_translateLeft a c η hc θ d e W t _
    (restrictionB_sourceTensorFiltration a c η hc θ d e hs W f hf)

noncomputable def sourceTensorFiltrationIdeal (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (W : ℤ) :
    Ideal (B a (SlopeArithmetic.slope c η) d ⊗[ℚ] B a (SlopeArithmetic.slope c η) e) :=
  additiveTensorFiltrationIdeal (sourceFiltration a c η hc θ d) (sourceFiltration a c η hc θ e)
    (sourceFiltration_mul_mem a c η hc θ d) (sourceFiltration_mul_mem a c η hc θ e) W

namespace SeparationInfinity

theorem separationCoefficient_filtration (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (θ : ℝ) (d e : I → ℕ) (hs : SlopeArithmetic.slope c η d=SlopeArithmetic.slope c η e)
    (W j : ℤ) (f : B a (SlopeArithmetic.slope c η) (d+e))
    (hf : f∈sourceFiltration a c η hc θ (d+e) W) :
    separationCoefficient a c η hc hs j f∈sourceTensorFiltration a c η hc θ d e W := by
  rw [separationCoefficient_apply]
  apply ElementaryPositivity.LaurentAtInfinity.mulPolynomialCoeff_mem
    (sourceTensorFiltrationIdeal a c η hc θ d e W)
  exact restrictionRelativeB_coeff_filtration a c η hc θ d e hs W f hf
end SeparationInfinity
end ElementaryPositivity.RawShuffle

end

end OAI
