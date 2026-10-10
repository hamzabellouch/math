import Mathlib
import OAI.Combinatorics.Chromatic.Walls.CenterLineSpecialization
import OAI.Combinatorics.Chromatic.Shuffle.SymbolDetection
import OAI.Combinatorics.Chromatic.Shuffle.CellSeparation

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity SeparationInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] cancelTensorRing cancelTensorAlg cancelFourRing cancelFourAlg
attribute [local instance] cancelTensorSelf cancelTensorNonUnital cancelFourNonUnital cancelSeriesRing
attribute [local instance] cellSepTensorSemiring cellSepTensorNonAssoc cellSepFourSemiring cellSepFourNonAssoc cellSepFourModule

lemma mappedInverseKernel_ratio {R : Type*} [CommRing R] [Algebra ℚ R]
    (a b : I → I → ℕ) (d e : I → ℕ) (f : S d⊗[ℚ]S e →ₐ[ℚ]R) :
    mapRing f.toRingHom ((inverseKernelUnit a d e)*(inverseKernelUnit b d e)⁻¹).val=
    (mappedInverseKernel a d e f).val * ((mappedInverseKernel b d e f)⁻¹).val := by
  rw [Units.val_mul,map_mul]
  rfl

lemma cellTransfer_normalized (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    ((inverseKernelUnit a (d₁+e₁) (d₂+e₂))*
      (inverseKernelUnit (fun _ _ : I=>0) (d₁+e₁) (d₂+e₂))⁻¹).val *
      polynomial (relativeTaylor (d₁+e₁) (d₂+e₂)
        (cellTransfer a d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂)))=
    ((-1 : ℚ)^eulerForm a d₂ e₁) •
      mapLinear (twoTargetTransfer a d₁ e₁ d₂ e₂) (fourInputSeries a d₁ e₁ d₂ e₂ f g) := by
  rw [cellTransfer,LinearMap.comp_apply,←twoTarget_polynomial_relativeTaylor,
    ←twoTarget_Laurent_projection a d₁ e₁ d₂ e₂ (firstCut d₁ e₁) (firstCut d₂ e₂),
    mappedInverseKernel_ratio,fourGrid_normalized]
  exact (mapLinear (twoTargetTransfer a d₁ e₁ d₂ e₂)).map_smul _ _

end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.LaurentAtInfinity
open SplitTree
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma eulerForm_transpose (a : I → I → ℕ) (d e : I → ℕ) :
    eulerForm (fun i j=>a j i) d e=eulerForm a e d := by
  unfold eulerForm
  congr 1
  · exact Finset.sum_congr rfl (fun i hi=>mul_comm _ _)
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring

namespace SeparationInfinity

noncomputable def mixedInverseKernelUnit (a b : I → I → ℕ)
    (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    (LaurentSeries (B a μ d⊗[ℚ] B a μ e))ˣ :=
  Units.map (mapRing (R:=S d⊗[ℚ]S e) (S:=B a μ d⊗[ℚ]B a μ e)
    (Algebra.TensorProduct.map (quotientAlg a μ d) (quotientAlg a μ e)).toRingHom).toMonoidHom
    (inverseKernelUnit b d e)

lemma pointed_mixedInverseKernel (a b : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    mapRing (pointedTensorRestriction a c η hc θ L R hL hR v w).toRingHom
      (mixedInverseKernelUnit a b (SlopeArithmetic.slope c η) L.dim R.dim).val =
    mapRing (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
      (mapRing (crossPointEval L R v w) (rawInverseKernelUnit b L.dim R.dim).val) := by
  apply HahnSeries.ext
  funext k
  change pointedTensorRestriction a c η hc θ L R hL hR v w
    (Algebra.TensorProduct.map (quotientAlg a (SlopeArithmetic.slope c η) L.dim)
      (quotientAlg a (SlopeArithmetic.slope c η) R.dim) ((inverseKernelUnit b L.dim R.dim).val.coeff k))=_
  rw [pointedTensorRestriction_quotient]
  have h:=congrArg (fun f : LaurentSeries (MvPolynomial (CellVars L.dim R.dim) ℚ)=>f.coeff k)
    (realize_inverseKernelUnit b L.dim R.dim)
  exact congrArg (fun f=>algebraMap ℚ _ (crossPointEval L R v w f)) h

lemma refined_mixedKernel_degreeZero (a b : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    mapRing (degreeZeroTensor a (SlopeArithmetic.slope c η) (.node L R)).toRingHom
      (mapRing (refinedAtB a c η hc θ L R hL hR v w).toRingHom
        (mixedInverseKernelUnit a b (SlopeArithmetic.slope c η) L.dim R.dim).val)=
      mapRing (algebraMap ℚ (tensor (quotientFamily a (SlopeArithmetic.slope c η)) (.node L R)))
        (scalarCrossKernel b L R v w).val := by
  trans mapRing (pointedTensorRestriction a c η hc θ L R hL hR v w).toRingHom
    (mixedInverseKernelUnit a b (SlopeArithmetic.slope c η) L.dim R.dim).val
  · apply HahnSeries.ext
    funext k
    exact degreeZero_refinedAtB a c η hc θ L R hL hR v w _
  · rw [pointed_mixedInverseKernel]
    congr 1
    exact congrArg Units.val (crossPointEval_inverseKernel_scalar b L R v w)

noncomputable def braidingRatioUnit (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d e : I → ℕ) : (LaurentSeries (B a μ d⊗[ℚ]B a μ e))ˣ :=
  mixedInverseKernelUnit a a μ d e *
    (mixedInverseKernelUnit a (fun i j=>a j i) μ d e)⁻¹

end SeparationInfinity

namespace SplitTree
omit [DecidableEq I] in
lemma scalarCrossKernel_transpose (a : I → I → ℕ) (c η : I → ℝ)
    (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ) (L R : SplitTree I)
    (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    scalarCrossKernel (fun i j=>a j i) L R v w=scalarCrossKernel a L R v w := by
  unfold scalarCrossKernel
  apply Finset.prod_congr rfl
  intro z hz
  apply Finset.prod_congr rfl
  intro t ht
  rw [eulerForm_transpose]
  congr 1
  obtain ⟨hz,hzs⟩:=L.leafDimension_onSlope c η θ hL z
  obtain ⟨ht,hts⟩:=R.leafDimension_onSlope c η θ hR t
  exact (hχ _ _ hz ht hzs hts).symm
end SplitTree
namespace SeparationInfinity
lemma refined_braidingRatio_degreeZero (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (hχ : SlopeEulerSymmetric a c η θ)
    (L R : SplitTree I) (hL : L.OnSlope c η θ) (hR : R.OnSlope c η θ)
    (v : L.Centers → ℚ) (w : R.Centers → ℚ) :
    mapRing (degreeZeroTensor a (SlopeArithmetic.slope c η) (.node L R)).toRingHom
      (mapRing (refinedAtB a c η hc θ L R hL hR v w).toRingHom
        (braidingRatioUnit a (SlopeArithmetic.slope c η) L.dim R.dim).val)=1 := by
  let H := (mapRing (degreeZeroTensor a (SlopeArithmetic.slope c η) (.node L R)).toRingHom).comp
    (mapRing (refinedAtB a c η hc θ L R hL hR v w).toRingHom)
  let Φ := Units.map H.toMonoidHom
  have he : Φ (mixedInverseKernelUnit a a (SlopeArithmetic.slope c η) L.dim R.dim)=
      Φ (mixedInverseKernelUnit a (fun i j=>a j i) (SlopeArithmetic.slope c η) L.dim R.dim) := by
    apply Units.ext
    change H _=H _
    dsimp only [H,RingHom.comp_apply]
    rw [refined_mixedKernel_degreeZero,refined_mixedKernel_degreeZero,
      scalarCrossKernel_transpose a c η θ hχ L R hL hR]
  have hh : Φ (braidingRatioUnit a (SlopeArithmetic.slope c η) L.dim R.dim)=1 := by
    rw [braidingRatioUnit,map_mul,map_inv,he,mul_inv_cancel]
  exact congrArg Units.val hh
end SeparationInfinity
end ElementaryPositivity.RawShuffle

end

end OAI
